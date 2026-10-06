/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4C070C001Part001. -/


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

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_000`. -/
@[expose]
noncomputable def nb070AlphaDummy000 (A : Class) : Var :=
  (freshVar ((A).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_001`. -/
@[expose]
noncomputable def nb070AlphaDummy001 (A : Class) : Var :=
  (freshVar ((A).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_002`. -/
@[expose]
noncomputable def nb070AlphaDummy002 (A : Class) : Var :=
  (freshVar (({(nb070AlphaDummy000 A)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv (nb070AlphaDummy000 A)) (synCncs))
          (synWrex (nb070AlphaDummy001 A) A
            (Wff.classEq (Class.cv (nb070AlphaDummy000 A))
              (synCnc (synCpw1 (Class.cv (nb070AlphaDummy001 A)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_003`. -/
@[expose]
noncomputable def nb070AlphaDummy003 (x : Var) (A : Class) (b : Var) : Var :=
  (freshVar (({ b } : Finset Var) ∪ ((synWa (Wff.classMem (Class.cv b) (synCncs))
          (synWrex x A (Wff.classEq (Class.cv b) (synCnc (synCpw1 (Class.cv x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_004`. -/
@[expose]
noncomputable def nb070AlphaDummy004 (A : Class) : Var :=
  (freshVar (((Class.cab (nb070AlphaDummy002 A) (Wff.classEq
          (Class.cab (nb070AlphaDummy000 A)
            (synWa (Wff.classMem (Class.cv (nb070AlphaDummy000 A)) (synCncs))
              (synWrex (nb070AlphaDummy001 A) A
                (Wff.classEq (Class.cv (nb070AlphaDummy000 A))
                  (synCnc (synCpw1 (Class.cv (nb070AlphaDummy001 A))))))))
          (synCsn (Class.cv (nb070AlphaDummy002 A)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_005`. -/
@[expose]
noncomputable def nb070AlphaDummy005 (A : Class) : Var :=
  (freshVar (((Class.cab (nb070AlphaDummy002 A) (Wff.classEq
          (Class.cab (nb070AlphaDummy000 A)
            (synWa (Wff.classMem (Class.cv (nb070AlphaDummy000 A)) (synCncs))
              (synWrex (nb070AlphaDummy001 A) A
                (Wff.classEq (Class.cv (nb070AlphaDummy000 A))
                  (synCnc (synCpw1 (Class.cv (nb070AlphaDummy001 A))))))))
          (synCsn (Class.cv (nb070AlphaDummy002 A)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_006`. -/
@[expose]
noncomputable def nb070AlphaDummy006 (x : Var) (A : Class) (b : Var) : Var :=
  (freshVar (((Class.cab (nb070AlphaDummy003 x A b) (Wff.classEq (Class.cab b
            (synWa (Wff.classMem (Class.cv b) (synCncs)) (synWrex x A
                (Wff.classEq (Class.cv b) (synCnc (synCpw1 (Class.cv x)))))))
          (synCsn (Class.cv (nb070AlphaDummy003 x A b)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_007`. -/
@[expose]
noncomputable def nb070AlphaDummy007 (x : Var) (A : Class) (b : Var) : Var :=
  (freshVar (((Class.cab (nb070AlphaDummy003 x A b) (Wff.classEq (Class.cab b
            (synWa (Wff.classMem (Class.cv b) (synCncs)) (synWrex x A
                (Wff.classEq (Class.cv b) (synCnc (synCpw1 (Class.cv x)))))))
          (synCsn (Class.cv (nb070AlphaDummy003 x A b)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_008`. -/
@[expose]
noncomputable def nb070AlphaDummy008 (A : Class) : Var :=
  (freshVar (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb070AlphaDummy001 A))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_009`. -/
@[expose]
noncomputable def nb070AlphaDummy009 (A : Class) : Var :=
  (freshVar (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb070AlphaDummy001 A))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_010`. -/
@[expose]
noncomputable def nb070AlphaDummy010 (x : Var) : Var :=
  (freshVar (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_011`. -/
@[expose]
noncomputable def nb070AlphaDummy011 (x : Var) : Var :=
  (freshVar (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv x)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_012`. -/
@[expose]
noncomputable def nb070AlphaDummy012 (A : Class) : Var :=
  (freshVar (((synCpw1 (Class.cv (nb070AlphaDummy001 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_013`. -/
@[expose]
noncomputable def nb070AlphaDummy013 (x : Var) : Var :=
  (freshVar (((synCpw1 (Class.cv x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_014`. -/
@[expose]
noncomputable def nb070AlphaDummy014 (A : Class) : Var :=
  (freshVar (((synCnin (synCpw (Class.cv (nb070AlphaDummy001 A))) (synC1c))).fv ∪
      ((synCnin (synCpw (Class.cv (nb070AlphaDummy001 A))) (synC1c))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_015`. -/
@[expose]
noncomputable def nb070AlphaDummy015 (x : Var) : Var :=
  (freshVar (((synCnin (synCpw (Class.cv x)) (synC1c))).fv ∪
      ((synCnin (synCpw (Class.cv x)) (synC1c))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_016`. -/
@[expose]
noncomputable def nb070AlphaDummy016 (A : Class) : Var :=
  (freshVar (((synCpw (Class.cv (nb070AlphaDummy001 A)))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_017`. -/
@[expose]
noncomputable def nb070AlphaDummy017 (x : Var) : Var :=
  (freshVar (((synCpw (Class.cv x))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_018`. -/
@[expose]
noncomputable def nb070AlphaDummy018 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy001 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_019`. -/
@[expose]
noncomputable def nb070AlphaDummy019 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_020`. -/
@[expose]
noncomputable def nb070AlphaDummy020 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb070AlphaDummy018 A))
          (Class.cv (nb070AlphaDummy001 A)))).fv ∪
      ((synCnin (Class.cv (nb070AlphaDummy018 A)) (Class.cv (nb070AlphaDummy001 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_021`. -/
@[expose]
noncomputable def nb070AlphaDummy021 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb070AlphaDummy019 x)) (Class.cv x))).fv ∪
      ((synCnin (Class.cv (nb070AlphaDummy019 x)) (Class.cv x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_022`. -/
@[expose]
noncomputable def nb070AlphaDummy022 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy018 A))).fv ∪
      ((Class.cv (nb070AlphaDummy001 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_023`. -/
@[expose]
noncomputable def nb070AlphaDummy023 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy019 x))).fv ∪ ((Class.cv x)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_024`. -/
@[expose]
noncomputable def nb070AlphaDummy024 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy009 A))).fv ∪
      ((Class.cv (nb070AlphaDummy008 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_025`. -/
@[expose]
noncomputable def nb070AlphaDummy025 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy009 A))).fv ∪
      ((Class.cv (nb070AlphaDummy008 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_026`. -/
@[expose]
noncomputable def nb070AlphaDummy026 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy011 x))).fv ∪
      ((Class.cv (nb070AlphaDummy010 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_027`. -/
@[expose]
noncomputable def nb070AlphaDummy027 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy011 x))).fv ∪
      ((Class.cv (nb070AlphaDummy010 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_028`. -/
@[expose]
noncomputable def nb070AlphaDummy028 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb070AlphaDummy024 A)
            (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy009 A))
              (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                (synCphi (Class.cv (nb070AlphaDummy025 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb070AlphaDummy024 A)
            (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy008 A))
              (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                (synCun (synCphi (Class.cv (nb070AlphaDummy025 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_029`. -/
@[expose]
noncomputable def nb070AlphaDummy029 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb070AlphaDummy026 x)
            (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy011 x))
              (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                (synCphi (Class.cv (nb070AlphaDummy027 x)))))))).fv ∪ ((synCcompl
          (Class.cab (nb070AlphaDummy026 x)
            (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy010 x))
              (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                (synCun (synCphi (Class.cv (nb070AlphaDummy027 x)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_030`. -/
@[expose]
noncomputable def nb070AlphaDummy030 (A : Class) : Var :=
  (freshVar (((Class.cab (nb070AlphaDummy024 A)
          (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy009 A))
            (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
              (synCphi (Class.cv (nb070AlphaDummy025 A))))))).fv ∪
      ((Class.cab (nb070AlphaDummy024 A)
          (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy009 A))
            (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
              (synCphi (Class.cv (nb070AlphaDummy025 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_031`. -/
@[expose]
noncomputable def nb070AlphaDummy031 (x : Var) : Var :=
  (freshVar (((Class.cab (nb070AlphaDummy026 x)
          (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy011 x))
            (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
              (synCphi (Class.cv (nb070AlphaDummy027 x))))))).fv ∪
      ((Class.cab (nb070AlphaDummy026 x)
          (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy011 x))
            (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
              (synCphi (Class.cv (nb070AlphaDummy027 x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_032`. -/
@[expose]
noncomputable def nb070AlphaDummy032 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy025 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_033`. -/
@[expose]
noncomputable def nb070AlphaDummy033 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy025 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_034`. -/
@[expose]
noncomputable def nb070AlphaDummy034 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy027 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_035`. -/
@[expose]
noncomputable def nb070AlphaDummy035 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy027 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_036`. -/
@[expose]
noncomputable def nb070AlphaDummy036 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb070AlphaDummy032 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb070AlphaDummy032 A)) (synC1c))).fv ∪
      ((Class.cv (nb070AlphaDummy032 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_037`. -/
@[expose]
noncomputable def nb070AlphaDummy037 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb070AlphaDummy034 x)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb070AlphaDummy034 x)) (synC1c))).fv ∪
      ((Class.cv (nb070AlphaDummy034 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_038`. -/
@[expose]
noncomputable def nb070AlphaDummy038 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_039`. -/
@[expose]
noncomputable def nb070AlphaDummy039 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_040`. -/
@[expose]
noncomputable def nb070AlphaDummy040 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_041`. -/
@[expose]
noncomputable def nb070AlphaDummy041 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_042`. -/
@[expose]
noncomputable def nb070AlphaDummy042 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_043`. -/
@[expose]
noncomputable def nb070AlphaDummy043 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_044`. -/
@[expose]
noncomputable def nb070AlphaDummy044 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb070AlphaDummy039 A))
          (Class.cv (nb070AlphaDummy040 A)))).fv ∪
      ((synCnin (Class.cv (nb070AlphaDummy039 A)) (Class.cv (nb070AlphaDummy040 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_045`. -/
@[expose]
noncomputable def nb070AlphaDummy045 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb070AlphaDummy042 x))
          (Class.cv (nb070AlphaDummy043 x)))).fv ∪
      ((synCnin (Class.cv (nb070AlphaDummy042 x)) (Class.cv (nb070AlphaDummy043 x)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_046`. -/
@[expose]
noncomputable def nb070AlphaDummy046 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy039 A))).fv ∪
      ((Class.cv (nb070AlphaDummy040 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_047`. -/
@[expose]
noncomputable def nb070AlphaDummy047 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy042 x))).fv ∪
      ((Class.cv (nb070AlphaDummy043 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_048`. -/
@[expose]
noncomputable def nb070AlphaDummy048 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb070AlphaDummy039 A)))).fv ∪
      ((synCcompl (Class.cv (nb070AlphaDummy040 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_049`. -/
@[expose]
noncomputable def nb070AlphaDummy049 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb070AlphaDummy042 x)))).fv ∪
      ((synCcompl (Class.cv (nb070AlphaDummy043 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_050`. -/
@[expose]
noncomputable def nb070AlphaDummy050 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy039 A))).fv ∪
      ((Class.cv (nb070AlphaDummy039 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_051`. -/
@[expose]
noncomputable def nb070AlphaDummy051 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy042 x))).fv ∪
      ((Class.cv (nb070AlphaDummy042 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_052`. -/
@[expose]
noncomputable def nb070AlphaDummy052 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy040 A))).fv ∪
      ((Class.cv (nb070AlphaDummy040 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_053`. -/
@[expose]
noncomputable def nb070AlphaDummy053 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy043 x))).fv ∪
      ((Class.cv (nb070AlphaDummy043 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_054`. -/
@[expose]
noncomputable def nb070AlphaDummy054 (A : Class) : Var :=
  (freshVar (((Class.cab (nb070AlphaDummy024 A)
          (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy008 A))
            (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
              (synCun (synCphi (Class.cv (nb070AlphaDummy025 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb070AlphaDummy024 A)
          (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy008 A))
            (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
              (synCun (synCphi (Class.cv (nb070AlphaDummy025 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_055`. -/
@[expose]
noncomputable def nb070AlphaDummy055 (x : Var) : Var :=
  (freshVar (((Class.cab (nb070AlphaDummy026 x)
          (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy010 x))
            (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
              (synCun (synCphi (Class.cv (nb070AlphaDummy027 x)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb070AlphaDummy026 x)
          (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy010 x))
            (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
              (synCun (synCphi (Class.cv (nb070AlphaDummy027 x)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_056`. -/
@[expose]
noncomputable def nb070AlphaDummy056 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb070AlphaDummy025 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_057`. -/
@[expose]
noncomputable def nb070AlphaDummy057 (x : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb070AlphaDummy027 x))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_058`. -/
@[expose]
noncomputable def nb070AlphaDummy058 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb070AlphaDummy025 A)))).fv ∪
      ((synCphi (Class.cv (nb070AlphaDummy025 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_059`. -/
@[expose]
noncomputable def nb070AlphaDummy059 (x : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb070AlphaDummy027 x)))).fv ∪
      ((synCphi (Class.cv (nb070AlphaDummy027 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_060`. -/
@[expose]
noncomputable def nb070AlphaDummy060 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy002 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb070_alpha_dummy_061`. -/
@[expose]
noncomputable def nb070AlphaDummy061 (x : Var) (A : Class) (b : Var) : Var :=
  (freshVar (((Class.cv (nb070AlphaDummy003 x A b))).fv) 0)

theorem nb070_fresh_000 (A : Class) :
    (nb070AlphaDummy004 A) ∉
      (((Class.cab (nb070AlphaDummy002 A) (Wff.classEq (Class.cab (nb070AlphaDummy000 A)
              (synWa (Wff.classMem (Class.cv (nb070AlphaDummy000 A)) (synCncs))
                (synWrex (nb070AlphaDummy001 A) A
                  (Wff.classEq (Class.cv (nb070AlphaDummy000 A))
                    (synCnc (synCpw1 (Class.cv (nb070AlphaDummy001 A))))))))
            (synCsn (Class.cv (nb070AlphaDummy002 A)))))).fv) :=
  by
  simpa only [nb070AlphaDummy004] using
    freshVar_not_mem
      (((Class.cab (nb070AlphaDummy002 A) (Wff.classEq (Class.cab (nb070AlphaDummy000 A)
              (synWa (Wff.classMem (Class.cv (nb070AlphaDummy000 A)) (synCncs))
                (synWrex (nb070AlphaDummy001 A) A
                  (Wff.classEq (Class.cv (nb070AlphaDummy000 A))
                    (synCnc (synCpw1 (Class.cv (nb070AlphaDummy001 A))))))))
            (synCsn (Class.cv (nb070AlphaDummy002 A)))))).fv)
      0

theorem nb070_fresh_001 (A : Class) :
    (nb070AlphaDummy005 A) ∉
      (((Class.cab (nb070AlphaDummy002 A) (Wff.classEq (Class.cab (nb070AlphaDummy000 A)
              (synWa (Wff.classMem (Class.cv (nb070AlphaDummy000 A)) (synCncs))
                (synWrex (nb070AlphaDummy001 A) A
                  (Wff.classEq (Class.cv (nb070AlphaDummy000 A))
                    (synCnc (synCpw1 (Class.cv (nb070AlphaDummy001 A))))))))
            (synCsn (Class.cv (nb070AlphaDummy002 A)))))).fv) :=
  by
  simpa only [nb070AlphaDummy005] using
    freshVar_not_mem
      (((Class.cab (nb070AlphaDummy002 A) (Wff.classEq (Class.cab (nb070AlphaDummy000 A)
              (synWa (Wff.classMem (Class.cv (nb070AlphaDummy000 A)) (synCncs))
                (synWrex (nb070AlphaDummy001 A) A
                  (Wff.classEq (Class.cv (nb070AlphaDummy000 A))
                    (synCnc (synCpw1 (Class.cv (nb070AlphaDummy001 A))))))))
            (synCsn (Class.cv (nb070AlphaDummy002 A)))))).fv)
      1

theorem nb070_distinct_002 (A : Class) :
    (nb070AlphaDummy004 A) ≠ (nb070AlphaDummy005 A) := by
  simpa only [nb070AlphaDummy004, nb070AlphaDummy005] using
    (freshVar_injective (((Class.cab (nb070AlphaDummy002 A) (Wff.classEq
            (Class.cab (nb070AlphaDummy000 A)
              (synWa (Wff.classMem (Class.cv (nb070AlphaDummy000 A)) (synCncs))
                (synWrex (nb070AlphaDummy001 A) A
                  (Wff.classEq (Class.cv (nb070AlphaDummy000 A))
                    (synCnc (synCpw1 (Class.cv (nb070AlphaDummy001 A))))))))
            (synCsn (Class.cv (nb070AlphaDummy002 A)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb070_fresh_003 (x : Var) (A : Class) (b : Var) :
    (nb070AlphaDummy006 x A b) ∉
      (((Class.cab (nb070AlphaDummy003 x A b) (Wff.classEq (Class.cab b
              (synWa (Wff.classMem (Class.cv b) (synCncs)) (synWrex x A
                  (Wff.classEq (Class.cv b) (synCnc (synCpw1 (Class.cv x)))))))
            (synCsn (Class.cv (nb070AlphaDummy003 x A b)))))).fv) :=
  by
  simpa only [nb070AlphaDummy006] using
    freshVar_not_mem
      (((Class.cab (nb070AlphaDummy003 x A b) (Wff.classEq (Class.cab b
              (synWa (Wff.classMem (Class.cv b) (synCncs)) (synWrex x A
                  (Wff.classEq (Class.cv b) (synCnc (synCpw1 (Class.cv x)))))))
            (synCsn (Class.cv (nb070AlphaDummy003 x A b)))))).fv)
      0

theorem nb070_fresh_004 (x : Var) (A : Class) (b : Var) :
    (nb070AlphaDummy007 x A b) ∉
      (((Class.cab (nb070AlphaDummy003 x A b) (Wff.classEq (Class.cab b
              (synWa (Wff.classMem (Class.cv b) (synCncs)) (synWrex x A
                  (Wff.classEq (Class.cv b) (synCnc (synCpw1 (Class.cv x)))))))
            (synCsn (Class.cv (nb070AlphaDummy003 x A b)))))).fv) :=
  by
  simpa only [nb070AlphaDummy007] using
    freshVar_not_mem
      (((Class.cab (nb070AlphaDummy003 x A b) (Wff.classEq (Class.cab b
              (synWa (Wff.classMem (Class.cv b) (synCncs)) (synWrex x A
                  (Wff.classEq (Class.cv b) (synCnc (synCpw1 (Class.cv x)))))))
            (synCsn (Class.cv (nb070AlphaDummy003 x A b)))))).fv)
      1

theorem nb070_distinct_005 (x : Var) (A : Class) (b : Var) :
    (nb070AlphaDummy006 x A b) ≠ (nb070AlphaDummy007 x A b) := by
  simpa only [nb070AlphaDummy006, nb070AlphaDummy007] using
    (freshVar_injective (((Class.cab (nb070AlphaDummy003 x A b) (Wff.classEq (Class.cab b
              (synWa (Wff.classMem (Class.cv b) (synCncs)) (synWrex x A
                  (Wff.classEq (Class.cv b) (synCnc (synCpw1 (Class.cv x)))))))
            (synCsn (Class.cv (nb070AlphaDummy003 x A b)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb070_fresh_006 (A : Class) :
    (nb070AlphaDummy054 A) ∉
      (((Class.cab (nb070AlphaDummy024 A)
            (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy008 A))
              (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                (synCun (synCphi (Class.cv (nb070AlphaDummy025 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb070AlphaDummy024 A)
            (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy008 A))
              (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                (synCun (synCphi (Class.cv (nb070AlphaDummy025 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb070AlphaDummy054] using
    freshVar_not_mem
      (((Class.cab (nb070AlphaDummy024 A)
            (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy008 A))
              (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                (synCun (synCphi (Class.cv (nb070AlphaDummy025 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb070AlphaDummy024 A)
            (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy008 A))
              (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                (synCun (synCphi (Class.cv (nb070AlphaDummy025 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb070_fresh_007 (A : Class) :
    (nb070AlphaDummy030 A) ∉
      (((Class.cab (nb070AlphaDummy024 A)
            (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy009 A))
              (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                (synCphi (Class.cv (nb070AlphaDummy025 A))))))).fv ∪
        ((Class.cab (nb070AlphaDummy024 A)
            (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy009 A))
              (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                (synCphi (Class.cv (nb070AlphaDummy025 A))))))).fv) :=
  by
  simpa only [nb070AlphaDummy030] using
    freshVar_not_mem
      (((Class.cab (nb070AlphaDummy024 A)
            (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy009 A))
              (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                (synCphi (Class.cv (nb070AlphaDummy025 A))))))).fv ∪
        ((Class.cab (nb070AlphaDummy024 A)
            (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy009 A))
              (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                (synCphi (Class.cv (nb070AlphaDummy025 A))))))).fv)
      0

theorem nb070_fresh_008 (x : Var) :
    (nb070AlphaDummy055 x) ∉
      (((Class.cab (nb070AlphaDummy026 x)
            (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy010 x))
              (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                (synCun (synCphi (Class.cv (nb070AlphaDummy027 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb070AlphaDummy026 x)
            (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy010 x))
              (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                (synCun (synCphi (Class.cv (nb070AlphaDummy027 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb070AlphaDummy055] using
    freshVar_not_mem
      (((Class.cab (nb070AlphaDummy026 x)
            (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy010 x))
              (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                (synCun (synCphi (Class.cv (nb070AlphaDummy027 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb070AlphaDummy026 x)
            (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy010 x))
              (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                (synCun (synCphi (Class.cv (nb070AlphaDummy027 x)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb070_fresh_009 (x : Var) :
    (nb070AlphaDummy031 x) ∉
      (((Class.cab (nb070AlphaDummy026 x)
            (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy011 x))
              (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                (synCphi (Class.cv (nb070AlphaDummy027 x))))))).fv ∪
        ((Class.cab (nb070AlphaDummy026 x)
            (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy011 x))
              (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                (synCphi (Class.cv (nb070AlphaDummy027 x))))))).fv) :=
  by
  simpa only [nb070AlphaDummy031] using
    freshVar_not_mem
      (((Class.cab (nb070AlphaDummy026 x)
            (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy011 x))
              (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                (synCphi (Class.cv (nb070AlphaDummy027 x))))))).fv ∪
        ((Class.cab (nb070AlphaDummy026 x)
            (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy011 x))
              (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                (synCphi (Class.cv (nb070AlphaDummy027 x))))))).fv)
      0

theorem nb070_fresh_010 (A : Class) :
    (nb070AlphaDummy018 A) ∉ (((Class.cv (nb070AlphaDummy001 A))).fv) := by
  simpa only [nb070AlphaDummy018] using
    freshVar_not_mem (((Class.cv (nb070AlphaDummy001 A))).fv) 0

theorem nb070_fresh_011 (A : Class) :
    (nb070AlphaDummy060 A) ∉ (((Class.cv (nb070AlphaDummy002 A))).fv) := by
  simpa only [nb070AlphaDummy060] using
    freshVar_not_mem (((Class.cv (nb070AlphaDummy002 A))).fv) 0

theorem nb070_fresh_012 (x : Var) (A : Class) (b : Var) :
    (nb070AlphaDummy061 x A b) ∉ (((Class.cv (nb070AlphaDummy003 x A b))).fv) := by
  simpa only [nb070AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb070AlphaDummy003 x A b))).fv) 0

theorem nb070_fresh_013 (A : Class) :
    (nb070AlphaDummy024 A) ∉
      (((Class.cv (nb070AlphaDummy009 A))).fv ∪ ((Class.cv (nb070AlphaDummy008 A))).fv) :=
  by
  simpa only [nb070AlphaDummy024] using
    freshVar_not_mem
      (((Class.cv (nb070AlphaDummy009 A))).fv ∪ ((Class.cv (nb070AlphaDummy008 A))).fv)
      0

theorem nb070_fresh_014 (A : Class) :
    (nb070AlphaDummy025 A) ∉
      (((Class.cv (nb070AlphaDummy009 A))).fv ∪ ((Class.cv (nb070AlphaDummy008 A))).fv) :=
  by
  simpa only [nb070AlphaDummy025] using
    freshVar_not_mem
      (((Class.cv (nb070AlphaDummy009 A))).fv ∪ ((Class.cv (nb070AlphaDummy008 A))).fv)
      1

theorem nb070_distinct_015 (A : Class) :
    (nb070AlphaDummy024 A) ≠ (nb070AlphaDummy025 A) := by
  simpa only [nb070AlphaDummy024, nb070AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb070AlphaDummy009 A))).fv ∪
        ((Class.cv (nb070AlphaDummy008 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb070_fresh_016 (x : Var) :
    (nb070AlphaDummy026 x) ∉
      (((Class.cv (nb070AlphaDummy011 x))).fv ∪ ((Class.cv (nb070AlphaDummy010 x))).fv) :=
  by
  simpa only [nb070AlphaDummy026] using
    freshVar_not_mem
      (((Class.cv (nb070AlphaDummy011 x))).fv ∪ ((Class.cv (nb070AlphaDummy010 x))).fv)
      0

theorem nb070_fresh_017 (x : Var) :
    (nb070AlphaDummy027 x) ∉
      (((Class.cv (nb070AlphaDummy011 x))).fv ∪ ((Class.cv (nb070AlphaDummy010 x))).fv) :=
  by
  simpa only [nb070AlphaDummy027] using
    freshVar_not_mem
      (((Class.cv (nb070AlphaDummy011 x))).fv ∪ ((Class.cv (nb070AlphaDummy010 x))).fv)
      1

theorem nb070_distinct_018 (x : Var) :
    (nb070AlphaDummy026 x) ≠ (nb070AlphaDummy027 x) := by
  simpa only [nb070AlphaDummy026, nb070AlphaDummy027] using
    (freshVar_injective (((Class.cv (nb070AlphaDummy011 x))).fv ∪
        ((Class.cv (nb070AlphaDummy010 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb070_fresh_019 (A : Class) :
    (nb070AlphaDummy022 A) ∉
      (((Class.cv (nb070AlphaDummy018 A))).fv ∪ ((Class.cv (nb070AlphaDummy001 A))).fv) :=
  by
  simpa only [nb070AlphaDummy022] using
    freshVar_not_mem
      (((Class.cv (nb070AlphaDummy018 A))).fv ∪ ((Class.cv (nb070AlphaDummy001 A))).fv)
      0

theorem nb070_fresh_020 (x : Var) :
    (nb070AlphaDummy023 x) ∉
      (((Class.cv (nb070AlphaDummy019 x))).fv ∪ ((Class.cv x)).fv) :=
  by
  simpa only [nb070AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb070AlphaDummy019 x))).fv ∪ ((Class.cv x)).fv) 0

theorem nb070_fresh_021 (A : Class) :
    (nb070AlphaDummy032 A) ∉ (((Class.cv (nb070AlphaDummy025 A))).fv) := by
  simpa only [nb070AlphaDummy032] using
    freshVar_not_mem (((Class.cv (nb070AlphaDummy025 A))).fv) 0

theorem nb070_fresh_022 (A : Class) :
    (nb070AlphaDummy033 A) ∉ (((Class.cv (nb070AlphaDummy025 A))).fv) := by
  simpa only [nb070AlphaDummy033] using
    freshVar_not_mem (((Class.cv (nb070AlphaDummy025 A))).fv) 1

theorem nb070_distinct_023 (A : Class) :
    (nb070AlphaDummy032 A) ≠ (nb070AlphaDummy033 A) := by
  simpa only [nb070AlphaDummy032, nb070AlphaDummy033] using
    (freshVar_injective (((Class.cv (nb070AlphaDummy025 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb070_fresh_024 (x : Var) :
    (nb070AlphaDummy034 x) ∉ (((Class.cv (nb070AlphaDummy027 x))).fv) := by
  simpa only [nb070AlphaDummy034] using
    freshVar_not_mem (((Class.cv (nb070AlphaDummy027 x))).fv) 0

theorem nb070_fresh_025 (x : Var) :
    (nb070AlphaDummy035 x) ∉ (((Class.cv (nb070AlphaDummy027 x))).fv) := by
  simpa only [nb070AlphaDummy035] using
    freshVar_not_mem (((Class.cv (nb070AlphaDummy027 x))).fv) 1

theorem nb070_distinct_026 (x : Var) :
    (nb070AlphaDummy034 x) ≠ (nb070AlphaDummy035 x) := by
  simpa only [nb070AlphaDummy034, nb070AlphaDummy035] using
    (freshVar_injective (((Class.cv (nb070AlphaDummy027 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb070_fresh_027 (A : Class) :
    (nb070AlphaDummy038 A) ∉
      (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb070AlphaDummy038] using
    freshVar_not_mem (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv) 0

theorem nb070_fresh_028 (A : Class) :
    (nb070AlphaDummy039 A) ∉
      (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb070AlphaDummy039] using
    freshVar_not_mem (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv) 1

theorem nb070_fresh_029 (A : Class) :
    (nb070AlphaDummy040 A) ∉
      (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb070AlphaDummy040] using
    freshVar_not_mem (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv) 2

theorem nb070_distinct_030 (A : Class) :
    (nb070AlphaDummy038 A) ≠ (nb070AlphaDummy039 A) := by
  simpa only [nb070AlphaDummy038, nb070AlphaDummy039] using
    (freshVar_injective (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb070_distinct_031 (A : Class) :
    (nb070AlphaDummy038 A) ≠ (nb070AlphaDummy040 A) := by
  simpa only [nb070AlphaDummy038, nb070AlphaDummy040] using
    (freshVar_injective (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb070_distinct_032 (A : Class) :
    (nb070AlphaDummy039 A) ≠ (nb070AlphaDummy040 A) := by
  simpa only [nb070AlphaDummy039, nb070AlphaDummy040] using
    (freshVar_injective (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb070_fresh_033 (x : Var) :
    (nb070AlphaDummy041 x) ∉
      (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb070AlphaDummy041] using
    freshVar_not_mem (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv) 0

theorem nb070_fresh_034 (x : Var) :
    (nb070AlphaDummy042 x) ∉
      (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb070AlphaDummy042] using
    freshVar_not_mem (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv) 1

theorem nb070_fresh_035 (x : Var) :
    (nb070AlphaDummy043 x) ∉
      (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb070AlphaDummy043] using
    freshVar_not_mem (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv) 2

theorem nb070_distinct_036 (x : Var) :
    (nb070AlphaDummy041 x) ≠ (nb070AlphaDummy042 x) := by
  simpa only [nb070AlphaDummy041, nb070AlphaDummy042] using
    (freshVar_injective (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb070_distinct_037 (x : Var) :
    (nb070AlphaDummy041 x) ≠ (nb070AlphaDummy043 x) := by
  simpa only [nb070AlphaDummy041, nb070AlphaDummy043] using
    (freshVar_injective (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb070_distinct_038 (x : Var) :
    (nb070AlphaDummy042 x) ≠ (nb070AlphaDummy043 x) := by
  simpa only [nb070AlphaDummy042, nb070AlphaDummy043] using
    (freshVar_injective (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb070_fresh_039 (A : Class) :
    (nb070AlphaDummy050 A) ∉
      (((Class.cv (nb070AlphaDummy039 A))).fv ∪ ((Class.cv (nb070AlphaDummy039 A))).fv) :=
  by
  simpa only [nb070AlphaDummy050] using
    freshVar_not_mem
      (((Class.cv (nb070AlphaDummy039 A))).fv ∪ ((Class.cv (nb070AlphaDummy039 A))).fv)
      0

theorem nb070_fresh_040 (A : Class) :
    (nb070AlphaDummy046 A) ∉
      (((Class.cv (nb070AlphaDummy039 A))).fv ∪ ((Class.cv (nb070AlphaDummy040 A))).fv) :=
  by
  simpa only [nb070AlphaDummy046] using
    freshVar_not_mem
      (((Class.cv (nb070AlphaDummy039 A))).fv ∪ ((Class.cv (nb070AlphaDummy040 A))).fv)
      0

theorem nb070_fresh_041 (A : Class) :
    (nb070AlphaDummy052 A) ∉
      (((Class.cv (nb070AlphaDummy040 A))).fv ∪ ((Class.cv (nb070AlphaDummy040 A))).fv) :=
  by
  simpa only [nb070AlphaDummy052] using
    freshVar_not_mem
      (((Class.cv (nb070AlphaDummy040 A))).fv ∪ ((Class.cv (nb070AlphaDummy040 A))).fv)
      0

theorem nb070_fresh_042 (x : Var) :
    (nb070AlphaDummy051 x) ∉
      (((Class.cv (nb070AlphaDummy042 x))).fv ∪ ((Class.cv (nb070AlphaDummy042 x))).fv) :=
  by
  simpa only [nb070AlphaDummy051] using
    freshVar_not_mem
      (((Class.cv (nb070AlphaDummy042 x))).fv ∪ ((Class.cv (nb070AlphaDummy042 x))).fv)
      0

theorem nb070_fresh_043 (x : Var) :
    (nb070AlphaDummy047 x) ∉
      (((Class.cv (nb070AlphaDummy042 x))).fv ∪ ((Class.cv (nb070AlphaDummy043 x))).fv) :=
  by
  simpa only [nb070AlphaDummy047] using
    freshVar_not_mem
      (((Class.cv (nb070AlphaDummy042 x))).fv ∪ ((Class.cv (nb070AlphaDummy043 x))).fv)
      0

theorem nb070_fresh_044 (x : Var) :
    (nb070AlphaDummy053 x) ∉
      (((Class.cv (nb070AlphaDummy043 x))).fv ∪ ((Class.cv (nb070AlphaDummy043 x))).fv) :=
  by
  simpa only [nb070AlphaDummy053] using
    freshVar_not_mem
      (((Class.cv (nb070AlphaDummy043 x))).fv ∪ ((Class.cv (nb070AlphaDummy043 x))).fv)
      0

theorem nb070_fresh_045 (x : Var) : (nb070AlphaDummy019 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb070AlphaDummy019] using freshVar_not_mem (((Class.cv x)).fv) 0

theorem nb070_fresh_046 (A : Class) :
    (nb070AlphaDummy036 A) ∉
      (((Wff.classMem (Class.cv (nb070AlphaDummy032 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb070AlphaDummy032 A)) (synC1c))).fv ∪
        ((Class.cv (nb070AlphaDummy032 A))).fv) :=
  by
  simpa only [nb070AlphaDummy036] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb070AlphaDummy032 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb070AlphaDummy032 A)) (synC1c))).fv ∪
        ((Class.cv (nb070AlphaDummy032 A))).fv)
      0

theorem nb070_fresh_047 (x : Var) :
    (nb070AlphaDummy037 x) ∉
      (((Wff.classMem (Class.cv (nb070AlphaDummy034 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb070AlphaDummy034 x)) (synC1c))).fv ∪
        ((Class.cv (nb070AlphaDummy034 x))).fv) :=
  by
  simpa only [nb070AlphaDummy037] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb070AlphaDummy034 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb070AlphaDummy034 x)) (synC1c))).fv ∪
        ((Class.cv (nb070AlphaDummy034 x))).fv)
      0

theorem nb070_fresh_048 (A : Class) :
    (nb070AlphaDummy028 A) ∉
      (((synCcompl (Class.cab (nb070AlphaDummy024 A)
              (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy009 A))
                (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                  (synCphi (Class.cv (nb070AlphaDummy025 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb070AlphaDummy024 A)
              (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy008 A))
                (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                  (synCun (synCphi (Class.cv (nb070AlphaDummy025 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb070AlphaDummy028] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb070AlphaDummy024 A)
              (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy009 A))
                (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                  (synCphi (Class.cv (nb070AlphaDummy025 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb070AlphaDummy024 A)
              (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy008 A))
                (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                  (synCun (synCphi (Class.cv (nb070AlphaDummy025 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb070_fresh_049 (x : Var) :
    (nb070AlphaDummy029 x) ∉
      (((synCcompl (Class.cab (nb070AlphaDummy026 x)
              (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy011 x))
                (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                  (synCphi (Class.cv (nb070AlphaDummy027 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb070AlphaDummy026 x)
              (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy010 x))
                (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                  (synCun (synCphi (Class.cv (nb070AlphaDummy027 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb070AlphaDummy029] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb070AlphaDummy026 x)
              (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy011 x))
                (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                  (synCphi (Class.cv (nb070AlphaDummy027 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb070AlphaDummy026 x)
              (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy010 x))
                (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                  (synCun (synCphi (Class.cv (nb070AlphaDummy027 x)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb070_fresh_050 (A : Class) :
    (nb070AlphaDummy048 A) ∉
      (((synCcompl (Class.cv (nb070AlphaDummy039 A)))).fv ∪
        ((synCcompl (Class.cv (nb070AlphaDummy040 A)))).fv) :=
  by
  simpa only [nb070AlphaDummy048] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb070AlphaDummy039 A)))).fv ∪
        ((synCcompl (Class.cv (nb070AlphaDummy040 A)))).fv)
      0

theorem nb070_fresh_051 (x : Var) :
    (nb070AlphaDummy049 x) ∉
      (((synCcompl (Class.cv (nb070AlphaDummy042 x)))).fv ∪
        ((synCcompl (Class.cv (nb070AlphaDummy043 x)))).fv) :=
  by
  simpa only [nb070AlphaDummy049] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb070AlphaDummy042 x)))).fv ∪
        ((synCcompl (Class.cv (nb070AlphaDummy043 x)))).fv)
      0

theorem nb070_fresh_052 (A : Class) :
    (nb070AlphaDummy056 A) ∉
      (((synCcompl (synCphi (Class.cv (nb070AlphaDummy025 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb070AlphaDummy056] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb070AlphaDummy025 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb070_fresh_053 (x : Var) :
    (nb070AlphaDummy057 x) ∉
      (((synCcompl (synCphi (Class.cv (nb070AlphaDummy027 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb070AlphaDummy057] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb070AlphaDummy027 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb070_fresh_054 (A : Class) :
    (nb070AlphaDummy008 A) ∉
      (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb070AlphaDummy001 A))))).fv) :=
  by
  simpa only [nb070AlphaDummy008] using
    freshVar_not_mem
      (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb070AlphaDummy001 A))))).fv) 0

theorem nb070_fresh_055 (A : Class) :
    (nb070AlphaDummy009 A) ∉
      (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb070AlphaDummy001 A))))).fv) :=
  by
  simpa only [nb070AlphaDummy009] using
    freshVar_not_mem
      (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb070AlphaDummy001 A))))).fv) 1

theorem nb070_distinct_056 (A : Class) :
    (nb070AlphaDummy008 A) ≠ (nb070AlphaDummy009 A) := by
  simpa only [nb070AlphaDummy008, nb070AlphaDummy009] using
    (freshVar_injective
      (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb070AlphaDummy001 A))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb070_fresh_057 (x : Var) :
    (nb070AlphaDummy010 x) ∉
      (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv x)))).fv) :=
  by
  simpa only [nb070AlphaDummy010] using
    freshVar_not_mem (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv x)))).fv) 0

theorem nb070_fresh_058 (x : Var) :
    (nb070AlphaDummy011 x) ∉
      (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv x)))).fv) :=
  by
  simpa only [nb070AlphaDummy011] using
    freshVar_not_mem (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv x)))).fv) 1

theorem nb070_distinct_059 (x : Var) :
    (nb070AlphaDummy010 x) ≠ (nb070AlphaDummy011 x) := by
  simpa only [nb070AlphaDummy010, nb070AlphaDummy011] using
    (freshVar_injective (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv x)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb070_fresh_060 (A : Class) :
    (nb070AlphaDummy020 A) ∉
      (((synCnin (Class.cv (nb070AlphaDummy018 A))
            (Class.cv (nb070AlphaDummy001 A)))).fv ∪
        ((synCnin (Class.cv (nb070AlphaDummy018 A))
            (Class.cv (nb070AlphaDummy001 A)))).fv) :=
  by
  simpa only [nb070AlphaDummy020] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb070AlphaDummy018 A))
            (Class.cv (nb070AlphaDummy001 A)))).fv ∪
        ((synCnin (Class.cv (nb070AlphaDummy018 A))
            (Class.cv (nb070AlphaDummy001 A)))).fv)
      0

theorem nb070_fresh_061 (x : Var) :
    (nb070AlphaDummy021 x) ∉
      (((synCnin (Class.cv (nb070AlphaDummy019 x)) (Class.cv x))).fv ∪
        ((synCnin (Class.cv (nb070AlphaDummy019 x)) (Class.cv x))).fv) :=
  by
  simpa only [nb070AlphaDummy021] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb070AlphaDummy019 x)) (Class.cv x))).fv ∪
        ((synCnin (Class.cv (nb070AlphaDummy019 x)) (Class.cv x))).fv)
      0

theorem nb070_fresh_062 (A : Class) :
    (nb070AlphaDummy044 A) ∉
      (((synCnin (Class.cv (nb070AlphaDummy039 A))
            (Class.cv (nb070AlphaDummy040 A)))).fv ∪
        ((synCnin (Class.cv (nb070AlphaDummy039 A))
            (Class.cv (nb070AlphaDummy040 A)))).fv) :=
  by
  simpa only [nb070AlphaDummy044] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb070AlphaDummy039 A))
            (Class.cv (nb070AlphaDummy040 A)))).fv ∪
        ((synCnin (Class.cv (nb070AlphaDummy039 A))
            (Class.cv (nb070AlphaDummy040 A)))).fv)
      0

theorem nb070_fresh_063 (x : Var) :
    (nb070AlphaDummy045 x) ∉
      (((synCnin (Class.cv (nb070AlphaDummy042 x))
            (Class.cv (nb070AlphaDummy043 x)))).fv ∪
        ((synCnin (Class.cv (nb070AlphaDummy042 x))
            (Class.cv (nb070AlphaDummy043 x)))).fv) :=
  by
  simpa only [nb070AlphaDummy045] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb070AlphaDummy042 x))
            (Class.cv (nb070AlphaDummy043 x)))).fv ∪
        ((synCnin (Class.cv (nb070AlphaDummy042 x))
            (Class.cv (nb070AlphaDummy043 x)))).fv)
      0

theorem nb070_fresh_064 (A : Class) :
    (nb070AlphaDummy014 A) ∉
      (((synCnin (synCpw (Class.cv (nb070AlphaDummy001 A))) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv (nb070AlphaDummy001 A))) (synC1c))).fv) :=
  by
  simpa only [nb070AlphaDummy014] using
    freshVar_not_mem
      (((synCnin (synCpw (Class.cv (nb070AlphaDummy001 A))) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv (nb070AlphaDummy001 A))) (synC1c))).fv)
      0

theorem nb070_fresh_065 (x : Var) :
    (nb070AlphaDummy015 x) ∉
      (((synCnin (synCpw (Class.cv x)) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv x)) (synC1c))).fv) :=
  by
  simpa only [nb070AlphaDummy015] using
    freshVar_not_mem
      (((synCnin (synCpw (Class.cv x)) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv x)) (synC1c))).fv)
      0

theorem nb070_fresh_066 (A : Class) :
    (nb070AlphaDummy058 A) ∉
      (((synCphi (Class.cv (nb070AlphaDummy025 A)))).fv ∪
        ((synCphi (Class.cv (nb070AlphaDummy025 A)))).fv) :=
  by
  simpa only [nb070AlphaDummy058] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb070AlphaDummy025 A)))).fv ∪
        ((synCphi (Class.cv (nb070AlphaDummy025 A)))).fv)
      0

theorem nb070_fresh_067 (x : Var) :
    (nb070AlphaDummy059 x) ∉
      (((synCphi (Class.cv (nb070AlphaDummy027 x)))).fv ∪
        ((synCphi (Class.cv (nb070AlphaDummy027 x)))).fv) :=
  by
  simpa only [nb070AlphaDummy059] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb070AlphaDummy027 x)))).fv ∪
        ((synCphi (Class.cv (nb070AlphaDummy027 x)))).fv)
      0

theorem nb070_fresh_068 (A : Class) :
    (nb070AlphaDummy016 A) ∉
      (((synCpw (Class.cv (nb070AlphaDummy001 A)))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb070AlphaDummy016] using
    freshVar_not_mem
      (((synCpw (Class.cv (nb070AlphaDummy001 A)))).fv ∪ ((synC1c)).fv) 0

theorem nb070_fresh_069 (x : Var) :
    (nb070AlphaDummy017 x) ∉ (((synCpw (Class.cv x))).fv ∪ ((synC1c)).fv) := by
  simpa only [nb070AlphaDummy017] using
    freshVar_not_mem (((synCpw (Class.cv x))).fv ∪ ((synC1c)).fv) 0

theorem nb070_fresh_070 (A : Class) :
    (nb070AlphaDummy012 A) ∉ (((synCpw1 (Class.cv (nb070AlphaDummy001 A)))).fv) :=
  by
  simpa only [nb070AlphaDummy012] using
    freshVar_not_mem (((synCpw1 (Class.cv (nb070AlphaDummy001 A)))).fv) 0

theorem nb070_fresh_071 (x : Var) :
    (nb070AlphaDummy013 x) ∉ (((synCpw1 (Class.cv x))).fv) := by
  simpa only [nb070AlphaDummy013] using
    freshVar_not_mem (((synCpw1 (Class.cv x))).fv) 0

theorem nb070_fresh_072 (A : Class) : (nb070AlphaDummy000 A) ∉ ((A).fv) := by
  simpa only [nb070AlphaDummy000] using freshVar_not_mem ((A).fv) 0

theorem nb070_fresh_073 (A : Class) : (nb070AlphaDummy001 A) ∉ ((A).fv) := by
  simpa only [nb070AlphaDummy001] using freshVar_not_mem ((A).fv) 1

theorem nb070_distinct_074 (A : Class) :
    (nb070AlphaDummy000 A) ≠ (nb070AlphaDummy001 A) := by
  simpa only [nb070AlphaDummy000, nb070AlphaDummy001] using
    (freshVar_injective ((A).fv) (i := 0) (j := 1) (by decide))

theorem nb070_fresh_075 (A : Class) :
    (nb070AlphaDummy002 A) ∉
      (({(nb070AlphaDummy000 A)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb070AlphaDummy000 A)) (synCncs))
            (synWrex (nb070AlphaDummy001 A) A
              (Wff.classEq (Class.cv (nb070AlphaDummy000 A))
                (synCnc (synCpw1 (Class.cv (nb070AlphaDummy001 A)))))))).fv) :=
  by
  simpa only [nb070AlphaDummy002] using
    freshVar_not_mem
      (({(nb070AlphaDummy000 A)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb070AlphaDummy000 A)) (synCncs))
            (synWrex (nb070AlphaDummy001 A) A
              (Wff.classEq (Class.cv (nb070AlphaDummy000 A))
                (synCnc (synCpw1 (Class.cv (nb070AlphaDummy001 A)))))))).fv)
      0

theorem nb070_fresh_076 (x : Var) (A : Class) (b : Var) :
    (nb070AlphaDummy003 x A b) ∉
      (({ b } : Finset Var) ∪ ((synWa (Wff.classMem (Class.cv b) (synCncs)) (synWrex x A
              (Wff.classEq (Class.cv b) (synCnc (synCpw1 (Class.cv x))))))).fv) :=
  by
  simpa only [nb070AlphaDummy003] using
    freshVar_not_mem
      (({ b } : Finset Var) ∪ ((synWa (Wff.classMem (Class.cv b) (synCncs)) (synWrex x A
              (Wff.classEq (Class.cv b) (synCnc (synCpw1 (Class.cv x))))))).fv)
      0

theorem nb070_support_mem_0000 (A : Class) :
    (nb070AlphaDummy018 A) ∈
      (((synCnin (Class.cv (nb070AlphaDummy018 A))
            (Class.cv (nb070AlphaDummy001 A)))).fv ∪
        ((synCnin (Class.cv (nb070AlphaDummy018 A))
            (Class.cv (nb070AlphaDummy001 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0001 (x : Var) :
    (nb070AlphaDummy019 x) ∈
      (((synCnin (Class.cv (nb070AlphaDummy019 x)) (Class.cv x))).fv ∪
        ((synCnin (Class.cv (nb070AlphaDummy019 x)) (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0002 (A : Class) :
    (nb070AlphaDummy018 A) ∈
      (((Class.cv (nb070AlphaDummy018 A))).fv ∪ ((Class.cv (nb070AlphaDummy001 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0003 (x : Var) :
    (nb070AlphaDummy019 x) ∈
      (((Class.cv (nb070AlphaDummy019 x))).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0004 (A : Class) :
    (nb070AlphaDummy001 A) ∈
      (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb070AlphaDummy001 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cpw1]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0005 (x : Var) :
    x ∈ (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cpw1]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0006 (A : Class) :
    (nb070AlphaDummy001 A) ∈ (((synCpw1 (Class.cv (nb070AlphaDummy001 A)))).fv) :=
  by
  rw [fv_syn_cpw1]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0007 (x : Var) : x ∈ (((synCpw1 (Class.cv x))).fv) :=
  by
  rw [fv_syn_cpw1]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0008 (A : Class) :
    (nb070AlphaDummy001 A) ∈
      (((synCnin (synCpw (Class.cv (nb070AlphaDummy001 A))) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv (nb070AlphaDummy001 A))) (synC1c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0009 (x : Var) :
    x ∈
      (((synCnin (synCpw (Class.cv x)) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv x)) (synC1c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0010 (A : Class) :
    (nb070AlphaDummy001 A) ∈
      (((synCpw (Class.cv (nb070AlphaDummy001 A)))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
