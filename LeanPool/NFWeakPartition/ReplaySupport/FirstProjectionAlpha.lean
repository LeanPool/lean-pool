/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001038Leaf1stReflected001. -/


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


namespace FirstProjectionAlpha

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
  (freshVar (({ alphaDummy000 } : Finset Var) ∪ ({ alphaDummy001 } : Finset Var) ∪
      ((synWex alphaDummy002 (Wff.classEq (Class.cv alphaDummy000)
            (synCop (Class.cv alphaDummy001) (Class.cv alphaDummy002))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_004`. -/
@[expose]
def alphaDummy004 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
      ((synWex z (Wff.classEq (Class.cv x) (synCop (Class.cv y) (Class.cv z))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_005`. -/
@[expose]
def alphaDummy005 : Var :=
  (freshVar (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy001)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_006`. -/
@[expose]
def alphaDummy006 : Var :=
  (freshVar (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy001)).fv) 1)

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
def alphaDummy009 : Var :=
  (freshVar (((synCcompl (Class.cab alphaDummy005
            (synWrex alphaDummy006 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy005)
                (synCphi (Class.cv alphaDummy006))))))).fv ∪ ((synCcompl
          (Class.cab alphaDummy005 (synWrex alphaDummy006 (Class.cv alphaDummy001)
              (Wff.classEq (Class.cv alphaDummy005)
                (synCun (synCphi (Class.cv alphaDummy006)) (synCsn (synC0c)))))))).fv) 0)

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
def alphaDummy011 : Var :=
  (freshVar (((Class.cab alphaDummy005 (synWrex alphaDummy006 (Class.cv alphaDummy000)
            (Wff.classEq (Class.cv alphaDummy005)
              (synCphi (Class.cv alphaDummy006)))))).fv ∪ ((Class.cab alphaDummy005
          (synWrex alphaDummy006 (Class.cv alphaDummy000)
            (Wff.classEq (Class.cv alphaDummy005)
              (synCphi (Class.cv alphaDummy006)))))).fv) 0)

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
def alphaDummy013 : Var :=
  (freshVar (((Class.cv alphaDummy006)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_014`. -/
@[expose]
def alphaDummy014 : Var :=
  (freshVar (((Class.cv alphaDummy006)).fv) 1)

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
def alphaDummy017 : Var :=
  (freshVar (((Wff.classMem (Class.cv alphaDummy013) (synCnnc))).fv ∪
        ((synCplc (Class.cv alphaDummy013) (synC1c))).fv ∪ ((Class.cv alphaDummy013)).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_018`. -/
@[expose]
def alphaDummy018 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alphaDummy015 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (alphaDummy015 x y)) (synC1c))).fv ∪
      ((Class.cv (alphaDummy015 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_019`. -/
@[expose]
def alphaDummy019 : Var :=
  (freshVar (((Class.cv alphaDummy013)).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_020`. -/
@[expose]
def alphaDummy020 : Var :=
  (freshVar (((Class.cv alphaDummy013)).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_021`. -/
@[expose]
def alphaDummy021 : Var :=
  (freshVar (((Class.cv alphaDummy013)).fv ∪ ((synC1c)).fv) 2)

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
def alphaDummy035 : Var :=
  (freshVar (((Class.cab alphaDummy005 (synWrex alphaDummy006 (Class.cv alphaDummy001)
            (Wff.classEq (Class.cv alphaDummy005)
              (synCun (synCphi (Class.cv alphaDummy006)) (synCsn (synC0c))))))).fv ∪
      ((Class.cab alphaDummy005 (synWrex alphaDummy006 (Class.cv alphaDummy001)
            (Wff.classEq (Class.cv alphaDummy005)
              (synCun (synCphi (Class.cv alphaDummy006)) (synCsn (synC0c))))))).fv) 0)

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
def alphaDummy037 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv alphaDummy006)))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_038`. -/
@[expose]
def alphaDummy038 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (alphaDummy008 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_039`. -/
@[expose]
def alphaDummy039 : Var :=
  (freshVar (((synCphi (Class.cv alphaDummy006))).fv ∪
      ((synCphi (Class.cv alphaDummy006))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_040`. -/
@[expose]
def alphaDummy040 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (alphaDummy008 x y)))).fv ∪
      ((synCphi (Class.cv (alphaDummy008 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_041`. -/
@[expose]
def alphaDummy041 : Var :=
  (freshVar (((Class.cv alphaDummy001)).fv ∪ ((Class.cv alphaDummy002)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_042`. -/
@[expose]
def alphaDummy042 : Var :=
  (freshVar (((Class.cv alphaDummy001)).fv ∪ ((Class.cv alphaDummy002)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_043`. -/
@[expose]
def alphaDummy043 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_044`. -/
@[expose]
def alphaDummy044 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_045`. -/
@[expose]
def alphaDummy045 : Var :=
  (freshVar (((synCcompl (Class.cab alphaDummy041
            (synWrex alphaDummy042 (Class.cv alphaDummy001)
              (Wff.classEq (Class.cv alphaDummy041)
                (synCphi (Class.cv alphaDummy042))))))).fv ∪ ((synCcompl
          (Class.cab alphaDummy041 (synWrex alphaDummy042 (Class.cv alphaDummy002)
              (Wff.classEq (Class.cv alphaDummy041)
                (synCun (synCphi (Class.cv alphaDummy042)) (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_046`. -/
@[expose]
def alphaDummy046 (y : Var) (z : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (alphaDummy043 y z)
            (synWrex (alphaDummy044 y z) (Class.cv y)
              (Wff.classEq (Class.cv (alphaDummy043 y z))
                (synCphi (Class.cv (alphaDummy044 y z)))))))).fv ∪ ((synCcompl
          (Class.cab (alphaDummy043 y z) (synWrex (alphaDummy044 y z) (Class.cv z)
              (Wff.classEq (Class.cv (alphaDummy043 y z))
                (synCun (synCphi (Class.cv (alphaDummy044 y z)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_047`. -/
@[expose]
def alphaDummy047 : Var :=
  (freshVar (((Class.cab alphaDummy041 (synWrex alphaDummy042 (Class.cv alphaDummy001)
            (Wff.classEq (Class.cv alphaDummy041)
              (synCphi (Class.cv alphaDummy042)))))).fv ∪ ((Class.cab alphaDummy041
          (synWrex alphaDummy042 (Class.cv alphaDummy001)
            (Wff.classEq (Class.cv alphaDummy041)
              (synCphi (Class.cv alphaDummy042)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_048`. -/
@[expose]
def alphaDummy048 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (alphaDummy043 y z) (synWrex (alphaDummy044 y z) (Class.cv y)
            (Wff.classEq (Class.cv (alphaDummy043 y z))
              (synCphi (Class.cv (alphaDummy044 y z))))))).fv ∪
      ((Class.cab (alphaDummy043 y z) (synWrex (alphaDummy044 y z) (Class.cv y)
            (Wff.classEq (Class.cv (alphaDummy043 y z))
              (synCphi (Class.cv (alphaDummy044 y z))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_049`. -/
@[expose]
def alphaDummy049 : Var :=
  (freshVar (((Class.cv alphaDummy042)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_050`. -/
@[expose]
def alphaDummy050 : Var :=
  (freshVar (((Class.cv alphaDummy042)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_051`. -/
@[expose]
def alphaDummy051 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy044 y z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_052`. -/
@[expose]
def alphaDummy052 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy044 y z))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_053`. -/
@[expose]
def alphaDummy053 : Var :=
  (freshVar (((Wff.classMem (Class.cv alphaDummy049) (synCnnc))).fv ∪
        ((synCplc (Class.cv alphaDummy049) (synC1c))).fv ∪ ((Class.cv alphaDummy049)).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_054`. -/
@[expose]
def alphaDummy054 (y : Var) (z : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alphaDummy051 y z)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (alphaDummy051 y z)) (synC1c))).fv ∪
      ((Class.cv (alphaDummy051 y z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_055`. -/
@[expose]
def alphaDummy055 : Var :=
  (freshVar (((Class.cv alphaDummy049)).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_056`. -/
@[expose]
def alphaDummy056 : Var :=
  (freshVar (((Class.cv alphaDummy049)).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_057`. -/
@[expose]
def alphaDummy057 : Var :=
  (freshVar (((Class.cv alphaDummy049)).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_058`. -/
@[expose]
def alphaDummy058 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy051 y z))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_059`. -/
@[expose]
def alphaDummy059 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy051 y z))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_060`. -/
@[expose]
def alphaDummy060 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy051 y z))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_071`. -/
@[expose]
def alphaDummy071 : Var :=
  (freshVar (((Class.cab alphaDummy041 (synWrex alphaDummy042 (Class.cv alphaDummy002)
            (Wff.classEq (Class.cv alphaDummy041)
              (synCun (synCphi (Class.cv alphaDummy042)) (synCsn (synC0c))))))).fv ∪
      ((Class.cab alphaDummy041 (synWrex alphaDummy042 (Class.cv alphaDummy002)
            (Wff.classEq (Class.cv alphaDummy041)
              (synCun (synCphi (Class.cv alphaDummy042)) (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_072`. -/
@[expose]
def alphaDummy072 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (alphaDummy043 y z) (synWrex (alphaDummy044 y z) (Class.cv z)
            (Wff.classEq (Class.cv (alphaDummy043 y z))
              (synCun (synCphi (Class.cv (alphaDummy044 y z))) (synCsn (synC0c))))))).fv ∪
      ((Class.cab (alphaDummy043 y z) (synWrex (alphaDummy044 y z) (Class.cv z)
            (Wff.classEq (Class.cv (alphaDummy043 y z))
              (synCun (synCphi (Class.cv (alphaDummy044 y z))) (synCsn (synC0c))))))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_073`. -/
@[expose]
def alphaDummy073 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv alphaDummy042)))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_074`. -/
@[expose]
def alphaDummy074 (y : Var) (z : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (alphaDummy044 y z))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_075`. -/
@[expose]
def alphaDummy075 : Var :=
  (freshVar (((synCphi (Class.cv alphaDummy042))).fv ∪
      ((synCphi (Class.cv alphaDummy042))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_076`. -/
@[expose]
def alphaDummy076 (y : Var) (z : Var) : Var :=
  (freshVar (((synCphi (Class.cv (alphaDummy044 y z)))).fv ∪
      ((synCphi (Class.cv (alphaDummy044 y z)))).fv) 0)

theorem support_mem_0000 :
    alphaDummy000 ∈
      (({ alphaDummy000 } : Finset Var) ∪ ({ alphaDummy001 } : Finset Var) ∪
        ((synWex alphaDummy002 (Wff.classEq (Class.cv alphaDummy000)
              (synCop (Class.cv alphaDummy001) (Class.cv alphaDummy002))))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem support_mem_0001 (x : Var) (y : Var) (z : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((synWex z
            (Wff.classEq (Class.cv x) (synCop (Class.cv y) (Class.cv z))))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem support_mem_0002 :
    alphaDummy001 ∈
      (({ alphaDummy000 } : Finset Var) ∪ ({ alphaDummy001 } : Finset Var) ∪
        ((synWex alphaDummy002 (Wff.classEq (Class.cv alphaDummy000)
              (synCop (Class.cv alphaDummy001) (Class.cv alphaDummy002))))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem support_mem_0003 (x : Var) (y : Var) (z : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((synWex z
            (Wff.classEq (Class.cv x) (synCop (Class.cv y) (Class.cv z))))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem support_mem_0004 :
    alphaDummy000 ∈
      (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy001)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0005 :
    alphaDummy000 ∈
      (((synCcompl (Class.cab alphaDummy005
              (synWrex alphaDummy006 (Class.cv alphaDummy000)
                (Wff.classEq (Class.cv alphaDummy005)
                  (synCphi (Class.cv alphaDummy006))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy005 (synWrex alphaDummy006 (Class.cv alphaDummy001)
                (Wff.classEq (Class.cv alphaDummy005)
                  (synCun (synCphi (Class.cv alphaDummy006))
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

theorem support_mem_0008 :
    alphaDummy000 ∈
      (((Class.cab alphaDummy005 (synWrex alphaDummy006 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy005)
                (synCphi (Class.cv alphaDummy006)))))).fv ∪ ((Class.cab alphaDummy005
            (synWrex alphaDummy006 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy005)
                (synCphi (Class.cv alphaDummy006)))))).fv) :=
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

theorem support_mem_0010 : alphaDummy006 ∈ (((Class.cv alphaDummy006)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0011 (x : Var) (y : Var) :
    (alphaDummy008 x y) ∈ (((Class.cv (alphaDummy008 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0012 :
    alphaDummy013 ∈
      (((Wff.classMem (Class.cv alphaDummy013) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy013) (synC1c))).fv ∪
        ((Class.cv alphaDummy013)).fv) :=
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

theorem support_mem_0014 :
    alphaDummy013 ∈ (((Class.cv alphaDummy013)).fv ∪ ((synC1c)).fv) :=
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

theorem support_mem_0016 :
    alphaDummy020 ∈
      (((synCnin (Class.cv alphaDummy020) (Class.cv alphaDummy021))).fv ∪
        ((synCnin (Class.cv alphaDummy020) (Class.cv alphaDummy021))).fv) :=
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

theorem support_mem_0018 :
    alphaDummy020 ∈
      (((Class.cv alphaDummy020)).fv ∪ ((Class.cv alphaDummy021)).fv) :=
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

theorem support_mem_0020 :
    alphaDummy021 ∈
      (((synCnin (Class.cv alphaDummy020) (Class.cv alphaDummy021))).fv ∪
        ((synCnin (Class.cv alphaDummy020) (Class.cv alphaDummy021))).fv) :=
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

theorem support_mem_0022 :
    alphaDummy021 ∈
      (((Class.cv alphaDummy020)).fv ∪ ((Class.cv alphaDummy021)).fv) :=
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

theorem support_mem_0024 :
    alphaDummy020 ∈
      (((synCcompl (Class.cv alphaDummy020))).fv ∪
        ((synCcompl (Class.cv alphaDummy021))).fv) :=
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

theorem support_mem_0026 :
    alphaDummy020 ∈
      (((Class.cv alphaDummy020)).fv ∪ ((Class.cv alphaDummy020)).fv) :=
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

theorem support_mem_0028 :
    alphaDummy021 ∈
      (((synCcompl (Class.cv alphaDummy020))).fv ∪
        ((synCcompl (Class.cv alphaDummy021))).fv) :=
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

theorem support_mem_0030 :
    alphaDummy021 ∈
      (((Class.cv alphaDummy021)).fv ∪ ((Class.cv alphaDummy021)).fv) :=
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

theorem support_mem_0032 :
    alphaDummy001 ∈
      (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy001)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0033 :
    alphaDummy001 ∈
      (((synCcompl (Class.cab alphaDummy005
              (synWrex alphaDummy006 (Class.cv alphaDummy000)
                (Wff.classEq (Class.cv alphaDummy005)
                  (synCphi (Class.cv alphaDummy006))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy005 (synWrex alphaDummy006 (Class.cv alphaDummy001)
                (Wff.classEq (Class.cv alphaDummy005)
                  (synCun (synCphi (Class.cv alphaDummy006))
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

theorem support_mem_0036 :
    alphaDummy001 ∈
      (((Class.cab alphaDummy005 (synWrex alphaDummy006 (Class.cv alphaDummy001)
              (Wff.classEq (Class.cv alphaDummy005)
                (synCun (synCphi (Class.cv alphaDummy006)) (synCsn (synC0c))))))).fv ∪
        ((Class.cab alphaDummy005 (synWrex alphaDummy006 (Class.cv alphaDummy001)
              (Wff.classEq (Class.cv alphaDummy005)
                (synCun (synCphi (Class.cv alphaDummy006)) (synCsn (synC0c))))))).fv) :=
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

theorem support_mem_0038 :
    alphaDummy006 ∈
      (((synCcompl (synCphi (Class.cv alphaDummy006)))).fv ∪
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

theorem support_mem_0040 :
    alphaDummy006 ∈
      (((synCphi (Class.cv alphaDummy006))).fv ∪
        ((synCphi (Class.cv alphaDummy006))).fv) :=
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

theorem support_mem_0042 :
    alphaDummy001 ∈
      (((Class.cv alphaDummy001)).fv ∪ ((Class.cv alphaDummy002)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0043 :
    alphaDummy001 ∈
      (((synCcompl (Class.cab alphaDummy041
              (synWrex alphaDummy042 (Class.cv alphaDummy001)
                (Wff.classEq (Class.cv alphaDummy041)
                  (synCphi (Class.cv alphaDummy042))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy041 (synWrex alphaDummy042 (Class.cv alphaDummy002)
                (Wff.classEq (Class.cv alphaDummy041)
                  (synCun (synCphi (Class.cv alphaDummy042))
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

theorem support_mem_0044 (y : Var) (z : Var) :
    y ∈ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0045 (y : Var) (z : Var) :
    y ∈
      (((synCcompl (Class.cab (alphaDummy043 y z)
              (synWrex (alphaDummy044 y z) (Class.cv y)
                (Wff.classEq (Class.cv (alphaDummy043 y z))
                  (synCphi (Class.cv (alphaDummy044 y z)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy043 y z) (synWrex (alphaDummy044 y z) (Class.cv z)
                (Wff.classEq (Class.cv (alphaDummy043 y z))
                  (synCun (synCphi (Class.cv (alphaDummy044 y z)))
                    (synCsn (synC0c)))))))).fv) :=
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
    alphaDummy001 ∈
      (((Class.cab alphaDummy041 (synWrex alphaDummy042 (Class.cv alphaDummy001)
              (Wff.classEq (Class.cv alphaDummy041)
                (synCphi (Class.cv alphaDummy042)))))).fv ∪ ((Class.cab alphaDummy041
            (synWrex alphaDummy042 (Class.cv alphaDummy001)
              (Wff.classEq (Class.cv alphaDummy041)
                (synCphi (Class.cv alphaDummy042)))))).fv) :=
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
    y ∈
      (((Class.cab (alphaDummy043 y z) (synWrex (alphaDummy044 y z) (Class.cv y)
              (Wff.classEq (Class.cv (alphaDummy043 y z))
                (synCphi (Class.cv (alphaDummy044 y z))))))).fv ∪
        ((Class.cab (alphaDummy043 y z) (synWrex (alphaDummy044 y z) (Class.cv y)
              (Wff.classEq (Class.cv (alphaDummy043 y z))
                (synCphi (Class.cv (alphaDummy044 y z))))))).fv) :=
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

theorem support_mem_0048 : alphaDummy042 ∈ (((Class.cv alphaDummy042)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0049 (y : Var) (z : Var) :
    (alphaDummy044 y z) ∈ (((Class.cv (alphaDummy044 y z))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0050 :
    alphaDummy049 ∈
      (((Wff.classMem (Class.cv alphaDummy049) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy049) (synC1c))).fv ∪
        ((Class.cv alphaDummy049)).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0051 (y : Var) (z : Var) :
    (alphaDummy051 y z) ∈
      (((Wff.classMem (Class.cv (alphaDummy051 y z)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (alphaDummy051 y z)) (synC1c))).fv ∪
        ((Class.cv (alphaDummy051 y z))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0052 :
    alphaDummy049 ∈ (((Class.cv alphaDummy049)).fv ∪ ((synC1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0053 (y : Var) (z : Var) :
    (alphaDummy051 y z) ∈ (((Class.cv (alphaDummy051 y z))).fv ∪ ((synC1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0054 :
    alphaDummy056 ∈
      (((synCnin (Class.cv alphaDummy056) (Class.cv alphaDummy057))).fv ∪
        ((synCnin (Class.cv alphaDummy056) (Class.cv alphaDummy057))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0055 (y : Var) (z : Var) :
    (alphaDummy059 y z) ∈
      (((synCnin (Class.cv (alphaDummy059 y z)) (Class.cv (alphaDummy060 y z)))).fv ∪
        ((synCnin (Class.cv (alphaDummy059 y z)) (Class.cv (alphaDummy060 y z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0056 :
    alphaDummy056 ∈
      (((Class.cv alphaDummy056)).fv ∪ ((Class.cv alphaDummy057)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0057 (y : Var) (z : Var) :
    (alphaDummy059 y z) ∈
      (((Class.cv (alphaDummy059 y z))).fv ∪ ((Class.cv (alphaDummy060 y z))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0058 :
    alphaDummy057 ∈
      (((synCnin (Class.cv alphaDummy056) (Class.cv alphaDummy057))).fv ∪
        ((synCnin (Class.cv alphaDummy056) (Class.cv alphaDummy057))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0059 (y : Var) (z : Var) :
    (alphaDummy060 y z) ∈
      (((synCnin (Class.cv (alphaDummy059 y z)) (Class.cv (alphaDummy060 y z)))).fv ∪
        ((synCnin (Class.cv (alphaDummy059 y z)) (Class.cv (alphaDummy060 y z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0060 :
    alphaDummy057 ∈
      (((Class.cv alphaDummy056)).fv ∪ ((Class.cv alphaDummy057)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0061 (y : Var) (z : Var) :
    (alphaDummy060 y z) ∈
      (((Class.cv (alphaDummy059 y z))).fv ∪ ((Class.cv (alphaDummy060 y z))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0062 :
    alphaDummy056 ∈
      (((synCcompl (Class.cv alphaDummy056))).fv ∪
        ((synCcompl (Class.cv alphaDummy057))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0063 (y : Var) (z : Var) :
    (alphaDummy059 y z) ∈
      (((synCcompl (Class.cv (alphaDummy059 y z)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy060 y z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0064 :
    alphaDummy056 ∈
      (((Class.cv alphaDummy056)).fv ∪ ((Class.cv alphaDummy056)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0065 (y : Var) (z : Var) :
    (alphaDummy059 y z) ∈
      (((Class.cv (alphaDummy059 y z))).fv ∪ ((Class.cv (alphaDummy059 y z))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0066 :
    alphaDummy057 ∈
      (((synCcompl (Class.cv alphaDummy056))).fv ∪
        ((synCcompl (Class.cv alphaDummy057))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0067 (y : Var) (z : Var) :
    (alphaDummy060 y z) ∈
      (((synCcompl (Class.cv (alphaDummy059 y z)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy060 y z)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0068 :
    alphaDummy057 ∈
      (((Class.cv alphaDummy057)).fv ∪ ((Class.cv alphaDummy057)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0069 (y : Var) (z : Var) :
    (alphaDummy060 y z) ∈
      (((Class.cv (alphaDummy060 y z))).fv ∪ ((Class.cv (alphaDummy060 y z))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0070 :
    alphaDummy002 ∈
      (((Class.cv alphaDummy001)).fv ∪ ((Class.cv alphaDummy002)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0071 :
    alphaDummy002 ∈
      (((synCcompl (Class.cab alphaDummy041
              (synWrex alphaDummy042 (Class.cv alphaDummy001)
                (Wff.classEq (Class.cv alphaDummy041)
                  (synCphi (Class.cv alphaDummy042))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy041 (synWrex alphaDummy042 (Class.cv alphaDummy002)
                (Wff.classEq (Class.cv alphaDummy041)
                  (synCun (synCphi (Class.cv alphaDummy042))
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

theorem support_mem_0072 (y : Var) (z : Var) :
    z ∈ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0073 (y : Var) (z : Var) :
    z ∈
      (((synCcompl (Class.cab (alphaDummy043 y z)
              (synWrex (alphaDummy044 y z) (Class.cv y)
                (Wff.classEq (Class.cv (alphaDummy043 y z))
                  (synCphi (Class.cv (alphaDummy044 y z)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy043 y z) (synWrex (alphaDummy044 y z) (Class.cv z)
                (Wff.classEq (Class.cv (alphaDummy043 y z))
                  (synCun (synCphi (Class.cv (alphaDummy044 y z)))
                    (synCsn (synC0c)))))))).fv) :=
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
    alphaDummy002 ∈
      (((Class.cab alphaDummy041 (synWrex alphaDummy042 (Class.cv alphaDummy002)
              (Wff.classEq (Class.cv alphaDummy041)
                (synCun (synCphi (Class.cv alphaDummy042)) (synCsn (synC0c))))))).fv ∪
        ((Class.cab alphaDummy041 (synWrex alphaDummy042 (Class.cv alphaDummy002)
              (Wff.classEq (Class.cv alphaDummy041)
                (synCun (synCphi (Class.cv alphaDummy042)) (synCsn (synC0c))))))).fv) :=
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
    z ∈
      (((Class.cab (alphaDummy043 y z) (synWrex (alphaDummy044 y z) (Class.cv z)
              (Wff.classEq (Class.cv (alphaDummy043 y z))
                (synCun (synCphi (Class.cv (alphaDummy044 y z)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (alphaDummy043 y z)
            (synWrex (alphaDummy044 y z) (Class.cv z)
              (Wff.classEq (Class.cv (alphaDummy043 y z))
                (synCun (synCphi (Class.cv (alphaDummy044 y z)))
                  (synCsn (synC0c))))))).fv) :=
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
    alphaDummy042 ∈
      (((synCcompl (synCphi (Class.cv alphaDummy042)))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0077 (y : Var) (z : Var) :
    (alphaDummy044 y z) ∈
      (((synCcompl (synCphi (Class.cv (alphaDummy044 y z))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0078 :
    alphaDummy042 ∈
      (((synCphi (Class.cv alphaDummy042))).fv ∪
        ((synCphi (Class.cv alphaDummy042))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0079 (y : Var) (z : Var) :
    (alphaDummy044 y z) ∈
      (((synCphi (Class.cv (alphaDummy044 y z)))).fv ∪
        ((synCphi (Class.cv (alphaDummy044 y z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end FirstProjectionAlpha

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
