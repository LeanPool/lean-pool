/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C056C001Part001`. -/


section

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

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_000`. -/
@[expose]
noncomputable def nb056AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_001`. -/
@[expose]
noncomputable def nb056AlphaDummy001 : Var :=
  (freshVar (((synCnin (synCcom (Class.cv (nb056AlphaDummy000))
            (synCcnv (Class.cv (nb056AlphaDummy000)))) (synCid))).fv ∪ ((synCnin
          (synCcom (Class.cv (nb056AlphaDummy000))
            (synCcnv (Class.cv (nb056AlphaDummy000)))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_002`. -/
@[expose]
noncomputable def nb056AlphaDummy002 (f : Var) : Var :=
  (freshVar (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
      ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_003`. -/
@[expose]
noncomputable def nb056AlphaDummy003 : Var :=
  (freshVar (((synCcom (Class.cv (nb056AlphaDummy000))
          (synCcnv (Class.cv (nb056AlphaDummy000))))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_004`. -/
@[expose]
noncomputable def nb056AlphaDummy004 (f : Var) : Var :=
  (freshVar (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_005`. -/
@[expose]
noncomputable def nb056AlphaDummy005 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy000))).fv ∪
      ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_006`. -/
@[expose]
noncomputable def nb056AlphaDummy006 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy000))).fv ∪
      ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_007`. -/
@[expose]
noncomputable def nb056AlphaDummy007 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy000))).fv ∪
      ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_008`. -/
@[expose]
noncomputable def nb056AlphaDummy008 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_009`. -/
@[expose]
noncomputable def nb056AlphaDummy009 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_010`. -/
@[expose]
noncomputable def nb056AlphaDummy010 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_011`. -/
@[expose]
noncomputable def nb056AlphaDummy011 : Var :=
  (freshVar
    (({(nb056AlphaDummy005)} : Finset Var) ∪ ({(nb056AlphaDummy006)} : Finset Var) ∪
      ((synWex (nb056AlphaDummy007) (synWa (synWbr (Class.cv (nb056AlphaDummy005))
              (synCcnv (Class.cv (nb056AlphaDummy000))) (Class.cv (nb056AlphaDummy007)))
            (synWbr (Class.cv (nb056AlphaDummy007)) (Class.cv (nb056AlphaDummy000))
              (Class.cv (nb056AlphaDummy006)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_012`. -/
@[expose]
noncomputable def nb056AlphaDummy012 (f : Var) : Var :=
  (freshVar (({(nb056AlphaDummy008 f)} : Finset Var) ∪
        ({(nb056AlphaDummy009 f)} : Finset Var) ∪ ((synWex (nb056AlphaDummy010 f) (synWa
            (synWbr (Class.cv (nb056AlphaDummy008 f)) (synCcnv (Class.cv f))
              (Class.cv (nb056AlphaDummy010 f)))
            (synWbr (Class.cv (nb056AlphaDummy010 f)) (Class.cv f)
              (Class.cv (nb056AlphaDummy009 f)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_013`. -/
@[expose]
noncomputable def nb056AlphaDummy013 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy005))).fv ∪ ((Class.cv (nb056AlphaDummy006))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_014`. -/
@[expose]
noncomputable def nb056AlphaDummy014 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy005))).fv ∪ ((Class.cv (nb056AlphaDummy006))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_015`. -/
@[expose]
noncomputable def nb056AlphaDummy015 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy008 f))).fv ∪
      ((Class.cv (nb056AlphaDummy009 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_016`. -/
@[expose]
noncomputable def nb056AlphaDummy016 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy008 f))).fv ∪
      ((Class.cv (nb056AlphaDummy009 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_017`. -/
@[expose]
noncomputable def nb056AlphaDummy017 : Var :=
  (freshVar (((synCcompl (Class.cab (nb056AlphaDummy013)
            (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy005))
              (Wff.classEq (Class.cv (nb056AlphaDummy013))
                (synCphi (Class.cv (nb056AlphaDummy014)))))))).fv ∪ ((synCcompl
          (Class.cab (nb056AlphaDummy013)
            (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy006))
              (Wff.classEq (Class.cv (nb056AlphaDummy013))
                (synCun (synCphi (Class.cv (nb056AlphaDummy014)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_018`. -/
@[expose]
noncomputable def nb056AlphaDummy018 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb056AlphaDummy015 f)
            (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy008 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                (synCphi (Class.cv (nb056AlphaDummy016 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb056AlphaDummy015 f)
            (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy009 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy016 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_019`. -/
@[expose]
noncomputable def nb056AlphaDummy019 : Var :=
  (freshVar (((Class.cab (nb056AlphaDummy013)
          (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy005))
            (Wff.classEq (Class.cv (nb056AlphaDummy013))
              (synCphi (Class.cv (nb056AlphaDummy014))))))).fv ∪
      ((Class.cab (nb056AlphaDummy013)
          (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy005))
            (Wff.classEq (Class.cv (nb056AlphaDummy013))
              (synCphi (Class.cv (nb056AlphaDummy014))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_020`. -/
@[expose]
noncomputable def nb056AlphaDummy020 (f : Var) : Var :=
  (freshVar (((Class.cab (nb056AlphaDummy015 f)
          (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy008 f))
            (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
              (synCphi (Class.cv (nb056AlphaDummy016 f))))))).fv ∪
      ((Class.cab (nb056AlphaDummy015 f)
          (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy008 f))
            (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
              (synCphi (Class.cv (nb056AlphaDummy016 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_021`. -/
@[expose]
noncomputable def nb056AlphaDummy021 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy014))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_022`. -/
@[expose]
noncomputable def nb056AlphaDummy022 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy014))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_023`. -/
@[expose]
noncomputable def nb056AlphaDummy023 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy016 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_024`. -/
@[expose]
noncomputable def nb056AlphaDummy024 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy016 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_025`. -/
@[expose]
noncomputable def nb056AlphaDummy025 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb056AlphaDummy021)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb056AlphaDummy021)) (synC1c))).fv ∪
      ((Class.cv (nb056AlphaDummy021))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_026`. -/
@[expose]
noncomputable def nb056AlphaDummy026 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb056AlphaDummy023 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb056AlphaDummy023 f)) (synC1c))).fv ∪
      ((Class.cv (nb056AlphaDummy023 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_027`. -/
@[expose]
noncomputable def nb056AlphaDummy027 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_028`. -/
@[expose]
noncomputable def nb056AlphaDummy028 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_029`. -/
@[expose]
noncomputable def nb056AlphaDummy029 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_030`. -/
@[expose]
noncomputable def nb056AlphaDummy030 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_031`. -/
@[expose]
noncomputable def nb056AlphaDummy031 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_032`. -/
@[expose]
noncomputable def nb056AlphaDummy032 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_033`. -/
@[expose]
noncomputable def nb056AlphaDummy033 : Var :=
  (freshVar (((synCnin (Class.cv (nb056AlphaDummy028))
          (Class.cv (nb056AlphaDummy029)))).fv ∪
      ((synCnin (Class.cv (nb056AlphaDummy028)) (Class.cv (nb056AlphaDummy029)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_034`. -/
@[expose]
noncomputable def nb056AlphaDummy034 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb056AlphaDummy031 f))
          (Class.cv (nb056AlphaDummy032 f)))).fv ∪
      ((synCnin (Class.cv (nb056AlphaDummy031 f)) (Class.cv (nb056AlphaDummy032 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_035`. -/
@[expose]
noncomputable def nb056AlphaDummy035 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy028))).fv ∪ ((Class.cv (nb056AlphaDummy029))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_036`. -/
@[expose]
noncomputable def nb056AlphaDummy036 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy031 f))).fv ∪
      ((Class.cv (nb056AlphaDummy032 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_037`. -/
@[expose]
noncomputable def nb056AlphaDummy037 : Var :=
  (freshVar (((synCcompl (Class.cv (nb056AlphaDummy028)))).fv ∪
      ((synCcompl (Class.cv (nb056AlphaDummy029)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_038`. -/
@[expose]
noncomputable def nb056AlphaDummy038 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb056AlphaDummy031 f)))).fv ∪
      ((synCcompl (Class.cv (nb056AlphaDummy032 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_039`. -/
@[expose]
noncomputable def nb056AlphaDummy039 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy028))).fv ∪ ((Class.cv (nb056AlphaDummy028))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_040`. -/
@[expose]
noncomputable def nb056AlphaDummy040 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy031 f))).fv ∪
      ((Class.cv (nb056AlphaDummy031 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_041`. -/
@[expose]
noncomputable def nb056AlphaDummy041 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy029))).fv ∪ ((Class.cv (nb056AlphaDummy029))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_042`. -/
@[expose]
noncomputable def nb056AlphaDummy042 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy032 f))).fv ∪
      ((Class.cv (nb056AlphaDummy032 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_043`. -/
@[expose]
noncomputable def nb056AlphaDummy043 : Var :=
  (freshVar (((Class.cab (nb056AlphaDummy013)
          (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy006))
            (Wff.classEq (Class.cv (nb056AlphaDummy013))
              (synCun (synCphi (Class.cv (nb056AlphaDummy014)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy013)
          (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy006))
            (Wff.classEq (Class.cv (nb056AlphaDummy013))
              (synCun (synCphi (Class.cv (nb056AlphaDummy014)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_044`. -/
@[expose]
noncomputable def nb056AlphaDummy044 (f : Var) : Var :=
  (freshVar (((Class.cab (nb056AlphaDummy015 f)
          (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy009 f))
            (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
              (synCun (synCphi (Class.cv (nb056AlphaDummy016 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy015 f)
          (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy009 f))
            (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
              (synCun (synCphi (Class.cv (nb056AlphaDummy016 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_045`. -/
@[expose]
noncomputable def nb056AlphaDummy045 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb056AlphaDummy014))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_046`. -/
@[expose]
noncomputable def nb056AlphaDummy046 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb056AlphaDummy016 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_047`. -/
@[expose]
noncomputable def nb056AlphaDummy047 : Var :=
  (freshVar (((synCphi (Class.cv (nb056AlphaDummy014)))).fv ∪
      ((synCphi (Class.cv (nb056AlphaDummy014)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_048`. -/
@[expose]
noncomputable def nb056AlphaDummy048 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb056AlphaDummy016 f)))).fv ∪
      ((synCphi (Class.cv (nb056AlphaDummy016 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_049`. -/
@[expose]
noncomputable def nb056AlphaDummy049 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy005))).fv ∪ ((Class.cv (nb056AlphaDummy007))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_050`. -/
@[expose]
noncomputable def nb056AlphaDummy050 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy005))).fv ∪ ((Class.cv (nb056AlphaDummy007))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_051`. -/
@[expose]
noncomputable def nb056AlphaDummy051 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy008 f))).fv ∪
      ((Class.cv (nb056AlphaDummy010 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_052`. -/
@[expose]
noncomputable def nb056AlphaDummy052 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy008 f))).fv ∪
      ((Class.cv (nb056AlphaDummy010 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_053`. -/
@[expose]
noncomputable def nb056AlphaDummy053 : Var :=
  (freshVar (((synCcompl (Class.cab (nb056AlphaDummy049)
            (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy005))
              (Wff.classEq (Class.cv (nb056AlphaDummy049))
                (synCphi (Class.cv (nb056AlphaDummy050)))))))).fv ∪ ((synCcompl
          (Class.cab (nb056AlphaDummy049)
            (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy007))
              (Wff.classEq (Class.cv (nb056AlphaDummy049))
                (synCun (synCphi (Class.cv (nb056AlphaDummy050)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_054`. -/
@[expose]
noncomputable def nb056AlphaDummy054 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb056AlphaDummy051 f)
            (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy008 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                (synCphi (Class.cv (nb056AlphaDummy052 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb056AlphaDummy051 f)
            (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy010 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy052 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_055`. -/
@[expose]
noncomputable def nb056AlphaDummy055 : Var :=
  (freshVar (((Class.cab (nb056AlphaDummy049)
          (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy005))
            (Wff.classEq (Class.cv (nb056AlphaDummy049))
              (synCphi (Class.cv (nb056AlphaDummy050))))))).fv ∪
      ((Class.cab (nb056AlphaDummy049)
          (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy005))
            (Wff.classEq (Class.cv (nb056AlphaDummy049))
              (synCphi (Class.cv (nb056AlphaDummy050))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_056`. -/
@[expose]
noncomputable def nb056AlphaDummy056 (f : Var) : Var :=
  (freshVar (((Class.cab (nb056AlphaDummy051 f)
          (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy008 f))
            (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
              (synCphi (Class.cv (nb056AlphaDummy052 f))))))).fv ∪
      ((Class.cab (nb056AlphaDummy051 f)
          (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy008 f))
            (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
              (synCphi (Class.cv (nb056AlphaDummy052 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_057`. -/
@[expose]
noncomputable def nb056AlphaDummy057 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy050))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_058`. -/
@[expose]
noncomputable def nb056AlphaDummy058 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy050))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_059`. -/
@[expose]
noncomputable def nb056AlphaDummy059 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy052 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_060`. -/
@[expose]
noncomputable def nb056AlphaDummy060 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy052 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_061`. -/
@[expose]
noncomputable def nb056AlphaDummy061 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb056AlphaDummy057)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb056AlphaDummy057)) (synC1c))).fv ∪
      ((Class.cv (nb056AlphaDummy057))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_062`. -/
@[expose]
noncomputable def nb056AlphaDummy062 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb056AlphaDummy059 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb056AlphaDummy059 f)) (synC1c))).fv ∪
      ((Class.cv (nb056AlphaDummy059 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_063`. -/
@[expose]
noncomputable def nb056AlphaDummy063 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_064`. -/
@[expose]
noncomputable def nb056AlphaDummy064 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_065`. -/
@[expose]
noncomputable def nb056AlphaDummy065 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_066`. -/
@[expose]
noncomputable def nb056AlphaDummy066 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_067`. -/
@[expose]
noncomputable def nb056AlphaDummy067 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_068`. -/
@[expose]
noncomputable def nb056AlphaDummy068 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_069`. -/
@[expose]
noncomputable def nb056AlphaDummy069 : Var :=
  (freshVar (((synCnin (Class.cv (nb056AlphaDummy064))
          (Class.cv (nb056AlphaDummy065)))).fv ∪
      ((synCnin (Class.cv (nb056AlphaDummy064)) (Class.cv (nb056AlphaDummy065)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_070`. -/
@[expose]
noncomputable def nb056AlphaDummy070 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb056AlphaDummy067 f))
          (Class.cv (nb056AlphaDummy068 f)))).fv ∪
      ((synCnin (Class.cv (nb056AlphaDummy067 f)) (Class.cv (nb056AlphaDummy068 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_071`. -/
@[expose]
noncomputable def nb056AlphaDummy071 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy064))).fv ∪ ((Class.cv (nb056AlphaDummy065))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_072`. -/
@[expose]
noncomputable def nb056AlphaDummy072 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy067 f))).fv ∪
      ((Class.cv (nb056AlphaDummy068 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_073`. -/
@[expose]
noncomputable def nb056AlphaDummy073 : Var :=
  (freshVar (((synCcompl (Class.cv (nb056AlphaDummy064)))).fv ∪
      ((synCcompl (Class.cv (nb056AlphaDummy065)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_074`. -/
@[expose]
noncomputable def nb056AlphaDummy074 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb056AlphaDummy067 f)))).fv ∪
      ((synCcompl (Class.cv (nb056AlphaDummy068 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_075`. -/
@[expose]
noncomputable def nb056AlphaDummy075 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy064))).fv ∪ ((Class.cv (nb056AlphaDummy064))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_076`. -/
@[expose]
noncomputable def nb056AlphaDummy076 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy067 f))).fv ∪
      ((Class.cv (nb056AlphaDummy067 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_077`. -/
@[expose]
noncomputable def nb056AlphaDummy077 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy065))).fv ∪ ((Class.cv (nb056AlphaDummy065))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_078`. -/
@[expose]
noncomputable def nb056AlphaDummy078 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy068 f))).fv ∪
      ((Class.cv (nb056AlphaDummy068 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_079`. -/
@[expose]
noncomputable def nb056AlphaDummy079 : Var :=
  (freshVar (((Class.cab (nb056AlphaDummy049)
          (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy007))
            (Wff.classEq (Class.cv (nb056AlphaDummy049))
              (synCun (synCphi (Class.cv (nb056AlphaDummy050)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy049)
          (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy007))
            (Wff.classEq (Class.cv (nb056AlphaDummy049))
              (synCun (synCphi (Class.cv (nb056AlphaDummy050)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_080`. -/
@[expose]
noncomputable def nb056AlphaDummy080 (f : Var) : Var :=
  (freshVar (((Class.cab (nb056AlphaDummy051 f)
          (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy010 f))
            (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
              (synCun (synCphi (Class.cv (nb056AlphaDummy052 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy051 f)
          (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy010 f))
            (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
              (synCun (synCphi (Class.cv (nb056AlphaDummy052 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_081`. -/
@[expose]
noncomputable def nb056AlphaDummy081 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb056AlphaDummy050))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_082`. -/
@[expose]
noncomputable def nb056AlphaDummy082 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb056AlphaDummy052 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_083`. -/
@[expose]
noncomputable def nb056AlphaDummy083 : Var :=
  (freshVar (((synCphi (Class.cv (nb056AlphaDummy050)))).fv ∪
      ((synCphi (Class.cv (nb056AlphaDummy050)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_084`. -/
@[expose]
noncomputable def nb056AlphaDummy084 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb056AlphaDummy052 f)))).fv ∪
      ((synCphi (Class.cv (nb056AlphaDummy052 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_085`. -/
@[expose]
noncomputable def nb056AlphaDummy085 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy000))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_086`. -/
@[expose]
noncomputable def nb056AlphaDummy086 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy000))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_087`. -/
@[expose]
noncomputable def nb056AlphaDummy087 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_088`. -/
@[expose]
noncomputable def nb056AlphaDummy088 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_089`. -/
@[expose]
noncomputable def nb056AlphaDummy089 : Var :=
  (freshVar
    (({(nb056AlphaDummy085)} : Finset Var) ∪ ({(nb056AlphaDummy086)} : Finset Var) ∪
      ((synWbr (Class.cv (nb056AlphaDummy086)) (Class.cv (nb056AlphaDummy000))
          (Class.cv (nb056AlphaDummy085)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_090`. -/
@[expose]
noncomputable def nb056AlphaDummy090 (f : Var) : Var :=
  (freshVar (({(nb056AlphaDummy087 f)} : Finset Var) ∪
        ({(nb056AlphaDummy088 f)} : Finset Var) ∪
      ((synWbr (Class.cv (nb056AlphaDummy088 f)) (Class.cv f)
          (Class.cv (nb056AlphaDummy087 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_091`. -/
@[expose]
noncomputable def nb056AlphaDummy091 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy085))).fv ∪ ((Class.cv (nb056AlphaDummy086))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_092`. -/
@[expose]
noncomputable def nb056AlphaDummy092 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy085))).fv ∪ ((Class.cv (nb056AlphaDummy086))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_093`. -/
@[expose]
noncomputable def nb056AlphaDummy093 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy087 f))).fv ∪
      ((Class.cv (nb056AlphaDummy088 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_094`. -/
@[expose]
noncomputable def nb056AlphaDummy094 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy087 f))).fv ∪
      ((Class.cv (nb056AlphaDummy088 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_095`. -/
@[expose]
noncomputable def nb056AlphaDummy095 : Var :=
  (freshVar (((synCcompl (Class.cab (nb056AlphaDummy091)
            (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy085))
              (Wff.classEq (Class.cv (nb056AlphaDummy091))
                (synCphi (Class.cv (nb056AlphaDummy092)))))))).fv ∪ ((synCcompl
          (Class.cab (nb056AlphaDummy091)
            (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy086))
              (Wff.classEq (Class.cv (nb056AlphaDummy091))
                (synCun (synCphi (Class.cv (nb056AlphaDummy092)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_096`. -/
@[expose]
noncomputable def nb056AlphaDummy096 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb056AlphaDummy093 f)
            (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                (synCphi (Class.cv (nb056AlphaDummy094 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb056AlphaDummy093 f)
            (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy094 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_097`. -/
@[expose]
noncomputable def nb056AlphaDummy097 : Var :=
  (freshVar (((Class.cab (nb056AlphaDummy091)
          (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy085))
            (Wff.classEq (Class.cv (nb056AlphaDummy091))
              (synCphi (Class.cv (nb056AlphaDummy092))))))).fv ∪
      ((Class.cab (nb056AlphaDummy091)
          (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy085))
            (Wff.classEq (Class.cv (nb056AlphaDummy091))
              (synCphi (Class.cv (nb056AlphaDummy092))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_098`. -/
@[expose]
noncomputable def nb056AlphaDummy098 (f : Var) : Var :=
  (freshVar (((Class.cab (nb056AlphaDummy093 f)
          (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy087 f))
            (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
              (synCphi (Class.cv (nb056AlphaDummy094 f))))))).fv ∪
      ((Class.cab (nb056AlphaDummy093 f)
          (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy087 f))
            (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
              (synCphi (Class.cv (nb056AlphaDummy094 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_099`. -/
@[expose]
noncomputable def nb056AlphaDummy099 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy092))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_100`. -/
@[expose]
noncomputable def nb056AlphaDummy100 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy092))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_101`. -/
@[expose]
noncomputable def nb056AlphaDummy101 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy094 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_102`. -/
@[expose]
noncomputable def nb056AlphaDummy102 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy094 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_103`. -/
@[expose]
noncomputable def nb056AlphaDummy103 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb056AlphaDummy099)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb056AlphaDummy099)) (synC1c))).fv ∪
      ((Class.cv (nb056AlphaDummy099))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_104`. -/
@[expose]
noncomputable def nb056AlphaDummy104 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb056AlphaDummy101 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb056AlphaDummy101 f)) (synC1c))).fv ∪
      ((Class.cv (nb056AlphaDummy101 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_105`. -/
@[expose]
noncomputable def nb056AlphaDummy105 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_106`. -/
@[expose]
noncomputable def nb056AlphaDummy106 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_107`. -/
@[expose]
noncomputable def nb056AlphaDummy107 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_108`. -/
@[expose]
noncomputable def nb056AlphaDummy108 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_109`. -/
@[expose]
noncomputable def nb056AlphaDummy109 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_110`. -/
@[expose]
noncomputable def nb056AlphaDummy110 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_111`. -/
@[expose]
noncomputable def nb056AlphaDummy111 : Var :=
  (freshVar (((synCnin (Class.cv (nb056AlphaDummy106))
          (Class.cv (nb056AlphaDummy107)))).fv ∪
      ((synCnin (Class.cv (nb056AlphaDummy106)) (Class.cv (nb056AlphaDummy107)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_112`. -/
@[expose]
noncomputable def nb056AlphaDummy112 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb056AlphaDummy109 f))
          (Class.cv (nb056AlphaDummy110 f)))).fv ∪
      ((synCnin (Class.cv (nb056AlphaDummy109 f)) (Class.cv (nb056AlphaDummy110 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_113`. -/
@[expose]
noncomputable def nb056AlphaDummy113 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy106))).fv ∪ ((Class.cv (nb056AlphaDummy107))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_114`. -/
@[expose]
noncomputable def nb056AlphaDummy114 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy109 f))).fv ∪
      ((Class.cv (nb056AlphaDummy110 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_115`. -/
@[expose]
noncomputable def nb056AlphaDummy115 : Var :=
  (freshVar (((synCcompl (Class.cv (nb056AlphaDummy106)))).fv ∪
      ((synCcompl (Class.cv (nb056AlphaDummy107)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_116`. -/
@[expose]
noncomputable def nb056AlphaDummy116 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb056AlphaDummy109 f)))).fv ∪
      ((synCcompl (Class.cv (nb056AlphaDummy110 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_117`. -/
@[expose]
noncomputable def nb056AlphaDummy117 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy106))).fv ∪ ((Class.cv (nb056AlphaDummy106))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_118`. -/
@[expose]
noncomputable def nb056AlphaDummy118 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy109 f))).fv ∪
      ((Class.cv (nb056AlphaDummy109 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_119`. -/
@[expose]
noncomputable def nb056AlphaDummy119 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy107))).fv ∪ ((Class.cv (nb056AlphaDummy107))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_120`. -/
@[expose]
noncomputable def nb056AlphaDummy120 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy110 f))).fv ∪
      ((Class.cv (nb056AlphaDummy110 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_121`. -/
@[expose]
noncomputable def nb056AlphaDummy121 : Var :=
  (freshVar (((Class.cab (nb056AlphaDummy091)
          (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy086))
            (Wff.classEq (Class.cv (nb056AlphaDummy091))
              (synCun (synCphi (Class.cv (nb056AlphaDummy092)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy091)
          (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy086))
            (Wff.classEq (Class.cv (nb056AlphaDummy091))
              (synCun (synCphi (Class.cv (nb056AlphaDummy092)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_122`. -/
@[expose]
noncomputable def nb056AlphaDummy122 (f : Var) : Var :=
  (freshVar (((Class.cab (nb056AlphaDummy093 f)
          (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy088 f))
            (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
              (synCun (synCphi (Class.cv (nb056AlphaDummy094 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy093 f)
          (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy088 f))
            (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
              (synCun (synCphi (Class.cv (nb056AlphaDummy094 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_123`. -/
@[expose]
noncomputable def nb056AlphaDummy123 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb056AlphaDummy092))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_124`. -/
@[expose]
noncomputable def nb056AlphaDummy124 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb056AlphaDummy094 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_125`. -/
@[expose]
noncomputable def nb056AlphaDummy125 : Var :=
  (freshVar (((synCphi (Class.cv (nb056AlphaDummy092)))).fv ∪
      ((synCphi (Class.cv (nb056AlphaDummy092)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_126`. -/
@[expose]
noncomputable def nb056AlphaDummy126 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb056AlphaDummy094 f)))).fv ∪
      ((synCphi (Class.cv (nb056AlphaDummy094 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_127`. -/
@[expose]
noncomputable def nb056AlphaDummy127 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy086))).fv ∪ ((Class.cv (nb056AlphaDummy085))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_128`. -/
@[expose]
noncomputable def nb056AlphaDummy128 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy086))).fv ∪ ((Class.cv (nb056AlphaDummy085))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_129`. -/
@[expose]
noncomputable def nb056AlphaDummy129 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy088 f))).fv ∪
      ((Class.cv (nb056AlphaDummy087 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_130`. -/
@[expose]
noncomputable def nb056AlphaDummy130 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy088 f))).fv ∪
      ((Class.cv (nb056AlphaDummy087 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_131`. -/
@[expose]
noncomputable def nb056AlphaDummy131 : Var :=
  (freshVar (((synCcompl (Class.cab (nb056AlphaDummy127)
            (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy086))
              (Wff.classEq (Class.cv (nb056AlphaDummy127))
                (synCphi (Class.cv (nb056AlphaDummy128)))))))).fv ∪ ((synCcompl
          (Class.cab (nb056AlphaDummy127)
            (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy085))
              (Wff.classEq (Class.cv (nb056AlphaDummy127))
                (synCun (synCphi (Class.cv (nb056AlphaDummy128)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_132`. -/
@[expose]
noncomputable def nb056AlphaDummy132 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb056AlphaDummy129 f)
            (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                (synCphi (Class.cv (nb056AlphaDummy130 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb056AlphaDummy129 f)
            (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy130 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_133`. -/
@[expose]
noncomputable def nb056AlphaDummy133 : Var :=
  (freshVar (((Class.cab (nb056AlphaDummy127)
          (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy086))
            (Wff.classEq (Class.cv (nb056AlphaDummy127))
              (synCphi (Class.cv (nb056AlphaDummy128))))))).fv ∪
      ((Class.cab (nb056AlphaDummy127)
          (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy086))
            (Wff.classEq (Class.cv (nb056AlphaDummy127))
              (synCphi (Class.cv (nb056AlphaDummy128))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_134`. -/
@[expose]
noncomputable def nb056AlphaDummy134 (f : Var) : Var :=
  (freshVar (((Class.cab (nb056AlphaDummy129 f)
          (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy088 f))
            (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
              (synCphi (Class.cv (nb056AlphaDummy130 f))))))).fv ∪
      ((Class.cab (nb056AlphaDummy129 f)
          (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy088 f))
            (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
              (synCphi (Class.cv (nb056AlphaDummy130 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_135`. -/
@[expose]
noncomputable def nb056AlphaDummy135 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy128))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_136`. -/
@[expose]
noncomputable def nb056AlphaDummy136 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy128))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_137`. -/
@[expose]
noncomputable def nb056AlphaDummy137 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy130 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_138`. -/
@[expose]
noncomputable def nb056AlphaDummy138 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy130 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_139`. -/
@[expose]
noncomputable def nb056AlphaDummy139 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb056AlphaDummy135)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb056AlphaDummy135)) (synC1c))).fv ∪
      ((Class.cv (nb056AlphaDummy135))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_140`. -/
@[expose]
noncomputable def nb056AlphaDummy140 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb056AlphaDummy137 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb056AlphaDummy137 f)) (synC1c))).fv ∪
      ((Class.cv (nb056AlphaDummy137 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_141`. -/
@[expose]
noncomputable def nb056AlphaDummy141 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_142`. -/
@[expose]
noncomputable def nb056AlphaDummy142 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_143`. -/
@[expose]
noncomputable def nb056AlphaDummy143 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_144`. -/
@[expose]
noncomputable def nb056AlphaDummy144 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_145`. -/
@[expose]
noncomputable def nb056AlphaDummy145 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_146`. -/
@[expose]
noncomputable def nb056AlphaDummy146 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_147`. -/
@[expose]
noncomputable def nb056AlphaDummy147 : Var :=
  (freshVar (((synCnin (Class.cv (nb056AlphaDummy142))
          (Class.cv (nb056AlphaDummy143)))).fv ∪
      ((synCnin (Class.cv (nb056AlphaDummy142)) (Class.cv (nb056AlphaDummy143)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_148`. -/
@[expose]
noncomputable def nb056AlphaDummy148 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb056AlphaDummy145 f))
          (Class.cv (nb056AlphaDummy146 f)))).fv ∪
      ((synCnin (Class.cv (nb056AlphaDummy145 f)) (Class.cv (nb056AlphaDummy146 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_149`. -/
@[expose]
noncomputable def nb056AlphaDummy149 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy142))).fv ∪ ((Class.cv (nb056AlphaDummy143))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C056C001Part002`. -/


section

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

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_150`. -/
@[expose]
noncomputable def nb056AlphaDummy150 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy145 f))).fv ∪
      ((Class.cv (nb056AlphaDummy146 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_151`. -/
@[expose]
noncomputable def nb056AlphaDummy151 : Var :=
  (freshVar (((synCcompl (Class.cv (nb056AlphaDummy142)))).fv ∪
      ((synCcompl (Class.cv (nb056AlphaDummy143)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_152`. -/
@[expose]
noncomputable def nb056AlphaDummy152 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb056AlphaDummy145 f)))).fv ∪
      ((synCcompl (Class.cv (nb056AlphaDummy146 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_153`. -/
@[expose]
noncomputable def nb056AlphaDummy153 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy142))).fv ∪ ((Class.cv (nb056AlphaDummy142))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_154`. -/
@[expose]
noncomputable def nb056AlphaDummy154 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy145 f))).fv ∪
      ((Class.cv (nb056AlphaDummy145 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_155`. -/
@[expose]
noncomputable def nb056AlphaDummy155 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy143))).fv ∪ ((Class.cv (nb056AlphaDummy143))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_156`. -/
@[expose]
noncomputable def nb056AlphaDummy156 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy146 f))).fv ∪
      ((Class.cv (nb056AlphaDummy146 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_157`. -/
@[expose]
noncomputable def nb056AlphaDummy157 : Var :=
  (freshVar (((Class.cab (nb056AlphaDummy127)
          (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy085))
            (Wff.classEq (Class.cv (nb056AlphaDummy127))
              (synCun (synCphi (Class.cv (nb056AlphaDummy128)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy127)
          (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy085))
            (Wff.classEq (Class.cv (nb056AlphaDummy127))
              (synCun (synCphi (Class.cv (nb056AlphaDummy128)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_158`. -/
@[expose]
noncomputable def nb056AlphaDummy158 (f : Var) : Var :=
  (freshVar (((Class.cab (nb056AlphaDummy129 f)
          (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy087 f))
            (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
              (synCun (synCphi (Class.cv (nb056AlphaDummy130 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy129 f)
          (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy087 f))
            (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
              (synCun (synCphi (Class.cv (nb056AlphaDummy130 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_159`. -/
@[expose]
noncomputable def nb056AlphaDummy159 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb056AlphaDummy128))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_160`. -/
@[expose]
noncomputable def nb056AlphaDummy160 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb056AlphaDummy130 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_161`. -/
@[expose]
noncomputable def nb056AlphaDummy161 : Var :=
  (freshVar (((synCphi (Class.cv (nb056AlphaDummy128)))).fv ∪
      ((synCphi (Class.cv (nb056AlphaDummy128)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_162`. -/
@[expose]
noncomputable def nb056AlphaDummy162 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb056AlphaDummy130 f)))).fv ∪
      ((synCphi (Class.cv (nb056AlphaDummy130 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_163`. -/
@[expose]
noncomputable def nb056AlphaDummy163 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy007))).fv ∪ ((Class.cv (nb056AlphaDummy006))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_164`. -/
@[expose]
noncomputable def nb056AlphaDummy164 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy007))).fv ∪ ((Class.cv (nb056AlphaDummy006))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_165`. -/
@[expose]
noncomputable def nb056AlphaDummy165 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy010 f))).fv ∪
      ((Class.cv (nb056AlphaDummy009 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_166`. -/
@[expose]
noncomputable def nb056AlphaDummy166 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy010 f))).fv ∪
      ((Class.cv (nb056AlphaDummy009 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_167`. -/
@[expose]
noncomputable def nb056AlphaDummy167 : Var :=
  (freshVar (((synCcompl (Class.cab (nb056AlphaDummy163)
            (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy007))
              (Wff.classEq (Class.cv (nb056AlphaDummy163))
                (synCphi (Class.cv (nb056AlphaDummy164)))))))).fv ∪ ((synCcompl
          (Class.cab (nb056AlphaDummy163)
            (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy006))
              (Wff.classEq (Class.cv (nb056AlphaDummy163))
                (synCun (synCphi (Class.cv (nb056AlphaDummy164)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_168`. -/
@[expose]
noncomputable def nb056AlphaDummy168 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb056AlphaDummy165 f)
            (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy010 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                (synCphi (Class.cv (nb056AlphaDummy166 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb056AlphaDummy165 f)
            (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy009 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy166 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_169`. -/
@[expose]
noncomputable def nb056AlphaDummy169 : Var :=
  (freshVar (((Class.cab (nb056AlphaDummy163)
          (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy007))
            (Wff.classEq (Class.cv (nb056AlphaDummy163))
              (synCphi (Class.cv (nb056AlphaDummy164))))))).fv ∪
      ((Class.cab (nb056AlphaDummy163)
          (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy007))
            (Wff.classEq (Class.cv (nb056AlphaDummy163))
              (synCphi (Class.cv (nb056AlphaDummy164))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_170`. -/
@[expose]
noncomputable def nb056AlphaDummy170 (f : Var) : Var :=
  (freshVar (((Class.cab (nb056AlphaDummy165 f)
          (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy010 f))
            (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
              (synCphi (Class.cv (nb056AlphaDummy166 f))))))).fv ∪
      ((Class.cab (nb056AlphaDummy165 f)
          (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy010 f))
            (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
              (synCphi (Class.cv (nb056AlphaDummy166 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_171`. -/
@[expose]
noncomputable def nb056AlphaDummy171 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy164))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_172`. -/
@[expose]
noncomputable def nb056AlphaDummy172 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy164))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_173`. -/
@[expose]
noncomputable def nb056AlphaDummy173 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy166 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_174`. -/
@[expose]
noncomputable def nb056AlphaDummy174 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy166 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_175`. -/
@[expose]
noncomputable def nb056AlphaDummy175 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb056AlphaDummy171)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb056AlphaDummy171)) (synC1c))).fv ∪
      ((Class.cv (nb056AlphaDummy171))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_176`. -/
@[expose]
noncomputable def nb056AlphaDummy176 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb056AlphaDummy173 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb056AlphaDummy173 f)) (synC1c))).fv ∪
      ((Class.cv (nb056AlphaDummy173 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_177`. -/
@[expose]
noncomputable def nb056AlphaDummy177 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_178`. -/
@[expose]
noncomputable def nb056AlphaDummy178 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_179`. -/
@[expose]
noncomputable def nb056AlphaDummy179 : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_180`. -/
@[expose]
noncomputable def nb056AlphaDummy180 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_181`. -/
@[expose]
noncomputable def nb056AlphaDummy181 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_182`. -/
@[expose]
noncomputable def nb056AlphaDummy182 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_183`. -/
@[expose]
noncomputable def nb056AlphaDummy183 : Var :=
  (freshVar (((synCnin (Class.cv (nb056AlphaDummy178))
          (Class.cv (nb056AlphaDummy179)))).fv ∪
      ((synCnin (Class.cv (nb056AlphaDummy178)) (Class.cv (nb056AlphaDummy179)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_184`. -/
@[expose]
noncomputable def nb056AlphaDummy184 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb056AlphaDummy181 f))
          (Class.cv (nb056AlphaDummy182 f)))).fv ∪
      ((synCnin (Class.cv (nb056AlphaDummy181 f)) (Class.cv (nb056AlphaDummy182 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_185`. -/
@[expose]
noncomputable def nb056AlphaDummy185 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy178))).fv ∪ ((Class.cv (nb056AlphaDummy179))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_186`. -/
@[expose]
noncomputable def nb056AlphaDummy186 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy181 f))).fv ∪
      ((Class.cv (nb056AlphaDummy182 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_187`. -/
@[expose]
noncomputable def nb056AlphaDummy187 : Var :=
  (freshVar (((synCcompl (Class.cv (nb056AlphaDummy178)))).fv ∪
      ((synCcompl (Class.cv (nb056AlphaDummy179)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_188`. -/
@[expose]
noncomputable def nb056AlphaDummy188 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb056AlphaDummy181 f)))).fv ∪
      ((synCcompl (Class.cv (nb056AlphaDummy182 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_189`. -/
@[expose]
noncomputable def nb056AlphaDummy189 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy178))).fv ∪ ((Class.cv (nb056AlphaDummy178))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_190`. -/
@[expose]
noncomputable def nb056AlphaDummy190 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy181 f))).fv ∪
      ((Class.cv (nb056AlphaDummy181 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_191`. -/
@[expose]
noncomputable def nb056AlphaDummy191 : Var :=
  (freshVar
    (((Class.cv (nb056AlphaDummy179))).fv ∪ ((Class.cv (nb056AlphaDummy179))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_192`. -/
@[expose]
noncomputable def nb056AlphaDummy192 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056AlphaDummy182 f))).fv ∪
      ((Class.cv (nb056AlphaDummy182 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_193`. -/
@[expose]
noncomputable def nb056AlphaDummy193 : Var :=
  (freshVar (((Class.cab (nb056AlphaDummy163)
          (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy006))
            (Wff.classEq (Class.cv (nb056AlphaDummy163))
              (synCun (synCphi (Class.cv (nb056AlphaDummy164)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy163)
          (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy006))
            (Wff.classEq (Class.cv (nb056AlphaDummy163))
              (synCun (synCphi (Class.cv (nb056AlphaDummy164)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_194`. -/
@[expose]
noncomputable def nb056AlphaDummy194 (f : Var) : Var :=
  (freshVar (((Class.cab (nb056AlphaDummy165 f)
          (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy009 f))
            (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
              (synCun (synCphi (Class.cv (nb056AlphaDummy166 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy165 f)
          (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy009 f))
            (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
              (synCun (synCphi (Class.cv (nb056AlphaDummy166 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_195`. -/
@[expose]
noncomputable def nb056AlphaDummy195 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb056AlphaDummy164))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_196`. -/
@[expose]
noncomputable def nb056AlphaDummy196 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb056AlphaDummy166 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_197`. -/
@[expose]
noncomputable def nb056AlphaDummy197 : Var :=
  (freshVar (((synCphi (Class.cv (nb056AlphaDummy164)))).fv ∪
      ((synCphi (Class.cv (nb056AlphaDummy164)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb056_alpha_dummy_198`. -/
@[expose]
noncomputable def nb056AlphaDummy198 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb056AlphaDummy166 f)))).fv ∪
      ((synCphi (Class.cv (nb056AlphaDummy166 f)))).fv) 0)

theorem nb056_fresh_000 :
    (nb056AlphaDummy019) ∉
      (((Class.cab (nb056AlphaDummy013)
            (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy005))
              (Wff.classEq (Class.cv (nb056AlphaDummy013))
                (synCphi (Class.cv (nb056AlphaDummy014))))))).fv ∪
        ((Class.cab (nb056AlphaDummy013)
            (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy005))
              (Wff.classEq (Class.cv (nb056AlphaDummy013))
                (synCphi (Class.cv (nb056AlphaDummy014))))))).fv) :=
  by
  simpa only [nb056AlphaDummy019] using
    freshVar_not_mem
      (((Class.cab (nb056AlphaDummy013)
            (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy005))
              (Wff.classEq (Class.cv (nb056AlphaDummy013))
                (synCphi (Class.cv (nb056AlphaDummy014))))))).fv ∪
        ((Class.cab (nb056AlphaDummy013)
            (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy005))
              (Wff.classEq (Class.cv (nb056AlphaDummy013))
                (synCphi (Class.cv (nb056AlphaDummy014))))))).fv)
      0

theorem nb056_fresh_001 :
    (nb056AlphaDummy043) ∉
      (((Class.cab (nb056AlphaDummy013)
            (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy006))
              (Wff.classEq (Class.cv (nb056AlphaDummy013))
                (synCun (synCphi (Class.cv (nb056AlphaDummy014)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy013)
            (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy006))
              (Wff.classEq (Class.cv (nb056AlphaDummy013))
                (synCun (synCphi (Class.cv (nb056AlphaDummy014)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb056AlphaDummy043] using
    freshVar_not_mem
      (((Class.cab (nb056AlphaDummy013)
            (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy006))
              (Wff.classEq (Class.cv (nb056AlphaDummy013))
                (synCun (synCphi (Class.cv (nb056AlphaDummy014)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy013)
            (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy006))
              (Wff.classEq (Class.cv (nb056AlphaDummy013))
                (synCun (synCphi (Class.cv (nb056AlphaDummy014)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb056_fresh_002 (f : Var) :
    (nb056AlphaDummy020 f) ∉
      (((Class.cab (nb056AlphaDummy015 f)
            (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy008 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                (synCphi (Class.cv (nb056AlphaDummy016 f))))))).fv ∪
        ((Class.cab (nb056AlphaDummy015 f)
            (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy008 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                (synCphi (Class.cv (nb056AlphaDummy016 f))))))).fv) :=
  by
  simpa only [nb056AlphaDummy020] using
    freshVar_not_mem
      (((Class.cab (nb056AlphaDummy015 f)
            (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy008 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                (synCphi (Class.cv (nb056AlphaDummy016 f))))))).fv ∪
        ((Class.cab (nb056AlphaDummy015 f)
            (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy008 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                (synCphi (Class.cv (nb056AlphaDummy016 f))))))).fv)
      0

theorem nb056_fresh_003 (f : Var) :
    (nb056AlphaDummy044 f) ∉
      (((Class.cab (nb056AlphaDummy015 f)
            (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy009 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy016 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy015 f)
            (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy009 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy016 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb056AlphaDummy044] using
    freshVar_not_mem
      (((Class.cab (nb056AlphaDummy015 f)
            (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy009 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy016 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy015 f)
            (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy009 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy016 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb056_fresh_004 :
    (nb056AlphaDummy055) ∉
      (((Class.cab (nb056AlphaDummy049)
            (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy005))
              (Wff.classEq (Class.cv (nb056AlphaDummy049))
                (synCphi (Class.cv (nb056AlphaDummy050))))))).fv ∪
        ((Class.cab (nb056AlphaDummy049)
            (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy005))
              (Wff.classEq (Class.cv (nb056AlphaDummy049))
                (synCphi (Class.cv (nb056AlphaDummy050))))))).fv) :=
  by
  simpa only [nb056AlphaDummy055] using
    freshVar_not_mem
      (((Class.cab (nb056AlphaDummy049)
            (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy005))
              (Wff.classEq (Class.cv (nb056AlphaDummy049))
                (synCphi (Class.cv (nb056AlphaDummy050))))))).fv ∪
        ((Class.cab (nb056AlphaDummy049)
            (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy005))
              (Wff.classEq (Class.cv (nb056AlphaDummy049))
                (synCphi (Class.cv (nb056AlphaDummy050))))))).fv)
      0

theorem nb056_fresh_005 :
    (nb056AlphaDummy079) ∉
      (((Class.cab (nb056AlphaDummy049)
            (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy007))
              (Wff.classEq (Class.cv (nb056AlphaDummy049))
                (synCun (synCphi (Class.cv (nb056AlphaDummy050)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy049)
            (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy007))
              (Wff.classEq (Class.cv (nb056AlphaDummy049))
                (synCun (synCphi (Class.cv (nb056AlphaDummy050)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb056AlphaDummy079] using
    freshVar_not_mem
      (((Class.cab (nb056AlphaDummy049)
            (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy007))
              (Wff.classEq (Class.cv (nb056AlphaDummy049))
                (synCun (synCphi (Class.cv (nb056AlphaDummy050)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy049)
            (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy007))
              (Wff.classEq (Class.cv (nb056AlphaDummy049))
                (synCun (synCphi (Class.cv (nb056AlphaDummy050)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb056_fresh_006 (f : Var) :
    (nb056AlphaDummy056 f) ∉
      (((Class.cab (nb056AlphaDummy051 f)
            (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy008 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                (synCphi (Class.cv (nb056AlphaDummy052 f))))))).fv ∪
        ((Class.cab (nb056AlphaDummy051 f)
            (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy008 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                (synCphi (Class.cv (nb056AlphaDummy052 f))))))).fv) :=
  by
  simpa only [nb056AlphaDummy056] using
    freshVar_not_mem
      (((Class.cab (nb056AlphaDummy051 f)
            (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy008 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                (synCphi (Class.cv (nb056AlphaDummy052 f))))))).fv ∪
        ((Class.cab (nb056AlphaDummy051 f)
            (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy008 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                (synCphi (Class.cv (nb056AlphaDummy052 f))))))).fv)
      0

theorem nb056_fresh_007 (f : Var) :
    (nb056AlphaDummy080 f) ∉
      (((Class.cab (nb056AlphaDummy051 f)
            (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy010 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy052 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy051 f)
            (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy010 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy052 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb056AlphaDummy080] using
    freshVar_not_mem
      (((Class.cab (nb056AlphaDummy051 f)
            (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy010 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy052 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy051 f)
            (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy010 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy052 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb056_fresh_008 :
    (nb056AlphaDummy097) ∉
      (((Class.cab (nb056AlphaDummy091)
            (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy085))
              (Wff.classEq (Class.cv (nb056AlphaDummy091))
                (synCphi (Class.cv (nb056AlphaDummy092))))))).fv ∪
        ((Class.cab (nb056AlphaDummy091)
            (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy085))
              (Wff.classEq (Class.cv (nb056AlphaDummy091))
                (synCphi (Class.cv (nb056AlphaDummy092))))))).fv) :=
  by
  simpa only [nb056AlphaDummy097] using
    freshVar_not_mem
      (((Class.cab (nb056AlphaDummy091)
            (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy085))
              (Wff.classEq (Class.cv (nb056AlphaDummy091))
                (synCphi (Class.cv (nb056AlphaDummy092))))))).fv ∪
        ((Class.cab (nb056AlphaDummy091)
            (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy085))
              (Wff.classEq (Class.cv (nb056AlphaDummy091))
                (synCphi (Class.cv (nb056AlphaDummy092))))))).fv)
      0

theorem nb056_fresh_009 :
    (nb056AlphaDummy121) ∉
      (((Class.cab (nb056AlphaDummy091)
            (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy086))
              (Wff.classEq (Class.cv (nb056AlphaDummy091))
                (synCun (synCphi (Class.cv (nb056AlphaDummy092)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy091)
            (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy086))
              (Wff.classEq (Class.cv (nb056AlphaDummy091))
                (synCun (synCphi (Class.cv (nb056AlphaDummy092)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb056AlphaDummy121] using
    freshVar_not_mem
      (((Class.cab (nb056AlphaDummy091)
            (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy086))
              (Wff.classEq (Class.cv (nb056AlphaDummy091))
                (synCun (synCphi (Class.cv (nb056AlphaDummy092)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy091)
            (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy086))
              (Wff.classEq (Class.cv (nb056AlphaDummy091))
                (synCun (synCphi (Class.cv (nb056AlphaDummy092)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb056_fresh_010 (f : Var) :
    (nb056AlphaDummy098 f) ∉
      (((Class.cab (nb056AlphaDummy093 f)
            (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                (synCphi (Class.cv (nb056AlphaDummy094 f))))))).fv ∪
        ((Class.cab (nb056AlphaDummy093 f)
            (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                (synCphi (Class.cv (nb056AlphaDummy094 f))))))).fv) :=
  by
  simpa only [nb056AlphaDummy098] using
    freshVar_not_mem
      (((Class.cab (nb056AlphaDummy093 f)
            (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                (synCphi (Class.cv (nb056AlphaDummy094 f))))))).fv ∪
        ((Class.cab (nb056AlphaDummy093 f)
            (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                (synCphi (Class.cv (nb056AlphaDummy094 f))))))).fv)
      0

theorem nb056_fresh_011 (f : Var) :
    (nb056AlphaDummy122 f) ∉
      (((Class.cab (nb056AlphaDummy093 f)
            (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy094 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy093 f)
            (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy094 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb056AlphaDummy122] using
    freshVar_not_mem
      (((Class.cab (nb056AlphaDummy093 f)
            (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy094 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy093 f)
            (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy094 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb056_fresh_012 :
    (nb056AlphaDummy157) ∉
      (((Class.cab (nb056AlphaDummy127)
            (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy085))
              (Wff.classEq (Class.cv (nb056AlphaDummy127))
                (synCun (synCphi (Class.cv (nb056AlphaDummy128)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy127)
            (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy085))
              (Wff.classEq (Class.cv (nb056AlphaDummy127))
                (synCun (synCphi (Class.cv (nb056AlphaDummy128)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb056AlphaDummy157] using
    freshVar_not_mem
      (((Class.cab (nb056AlphaDummy127)
            (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy085))
              (Wff.classEq (Class.cv (nb056AlphaDummy127))
                (synCun (synCphi (Class.cv (nb056AlphaDummy128)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy127)
            (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy085))
              (Wff.classEq (Class.cv (nb056AlphaDummy127))
                (synCun (synCphi (Class.cv (nb056AlphaDummy128)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb056_fresh_013 :
    (nb056AlphaDummy133) ∉
      (((Class.cab (nb056AlphaDummy127)
            (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy086))
              (Wff.classEq (Class.cv (nb056AlphaDummy127))
                (synCphi (Class.cv (nb056AlphaDummy128))))))).fv ∪
        ((Class.cab (nb056AlphaDummy127)
            (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy086))
              (Wff.classEq (Class.cv (nb056AlphaDummy127))
                (synCphi (Class.cv (nb056AlphaDummy128))))))).fv) :=
  by
  simpa only [nb056AlphaDummy133] using
    freshVar_not_mem
      (((Class.cab (nb056AlphaDummy127)
            (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy086))
              (Wff.classEq (Class.cv (nb056AlphaDummy127))
                (synCphi (Class.cv (nb056AlphaDummy128))))))).fv ∪
        ((Class.cab (nb056AlphaDummy127)
            (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy086))
              (Wff.classEq (Class.cv (nb056AlphaDummy127))
                (synCphi (Class.cv (nb056AlphaDummy128))))))).fv)
      0

theorem nb056_fresh_014 (f : Var) :
    (nb056AlphaDummy158 f) ∉
      (((Class.cab (nb056AlphaDummy129 f)
            (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy130 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy129 f)
            (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy130 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb056AlphaDummy158] using
    freshVar_not_mem
      (((Class.cab (nb056AlphaDummy129 f)
            (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy130 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy129 f)
            (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy130 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb056_fresh_015 (f : Var) :
    (nb056AlphaDummy134 f) ∉
      (((Class.cab (nb056AlphaDummy129 f)
            (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                (synCphi (Class.cv (nb056AlphaDummy130 f))))))).fv ∪
        ((Class.cab (nb056AlphaDummy129 f)
            (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                (synCphi (Class.cv (nb056AlphaDummy130 f))))))).fv) :=
  by
  simpa only [nb056AlphaDummy134] using
    freshVar_not_mem
      (((Class.cab (nb056AlphaDummy129 f)
            (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                (synCphi (Class.cv (nb056AlphaDummy130 f))))))).fv ∪
        ((Class.cab (nb056AlphaDummy129 f)
            (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                (synCphi (Class.cv (nb056AlphaDummy130 f))))))).fv)
      0

theorem nb056_fresh_016 :
    (nb056AlphaDummy193) ∉
      (((Class.cab (nb056AlphaDummy163)
            (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy006))
              (Wff.classEq (Class.cv (nb056AlphaDummy163))
                (synCun (synCphi (Class.cv (nb056AlphaDummy164)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy163)
            (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy006))
              (Wff.classEq (Class.cv (nb056AlphaDummy163))
                (synCun (synCphi (Class.cv (nb056AlphaDummy164)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb056AlphaDummy193] using
    freshVar_not_mem
      (((Class.cab (nb056AlphaDummy163)
            (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy006))
              (Wff.classEq (Class.cv (nb056AlphaDummy163))
                (synCun (synCphi (Class.cv (nb056AlphaDummy164)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy163)
            (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy006))
              (Wff.classEq (Class.cv (nb056AlphaDummy163))
                (synCun (synCphi (Class.cv (nb056AlphaDummy164)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb056_fresh_017 :
    (nb056AlphaDummy169) ∉
      (((Class.cab (nb056AlphaDummy163)
            (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy007))
              (Wff.classEq (Class.cv (nb056AlphaDummy163))
                (synCphi (Class.cv (nb056AlphaDummy164))))))).fv ∪
        ((Class.cab (nb056AlphaDummy163)
            (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy007))
              (Wff.classEq (Class.cv (nb056AlphaDummy163))
                (synCphi (Class.cv (nb056AlphaDummy164))))))).fv) :=
  by
  simpa only [nb056AlphaDummy169] using
    freshVar_not_mem
      (((Class.cab (nb056AlphaDummy163)
            (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy007))
              (Wff.classEq (Class.cv (nb056AlphaDummy163))
                (synCphi (Class.cv (nb056AlphaDummy164))))))).fv ∪
        ((Class.cab (nb056AlphaDummy163)
            (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy007))
              (Wff.classEq (Class.cv (nb056AlphaDummy163))
                (synCphi (Class.cv (nb056AlphaDummy164))))))).fv)
      0

theorem nb056_fresh_018 (f : Var) :
    (nb056AlphaDummy194 f) ∉
      (((Class.cab (nb056AlphaDummy165 f)
            (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy009 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy166 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy165 f)
            (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy009 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy166 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb056AlphaDummy194] using
    freshVar_not_mem
      (((Class.cab (nb056AlphaDummy165 f)
            (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy009 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy166 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy165 f)
            (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy009 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy166 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb056_fresh_019 (f : Var) :
    (nb056AlphaDummy170 f) ∉
      (((Class.cab (nb056AlphaDummy165 f)
            (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy010 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                (synCphi (Class.cv (nb056AlphaDummy166 f))))))).fv ∪
        ((Class.cab (nb056AlphaDummy165 f)
            (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy010 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                (synCphi (Class.cv (nb056AlphaDummy166 f))))))).fv) :=
  by
  simpa only [nb056AlphaDummy170] using
    freshVar_not_mem
      (((Class.cab (nb056AlphaDummy165 f)
            (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy010 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                (synCphi (Class.cv (nb056AlphaDummy166 f))))))).fv ∪
        ((Class.cab (nb056AlphaDummy165 f)
            (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy010 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                (synCphi (Class.cv (nb056AlphaDummy166 f))))))).fv)
      0

theorem nb056_fresh_020 :
    (nb056AlphaDummy085) ∉ (((Class.cv (nb056AlphaDummy000))).fv) := by
  simpa only [nb056AlphaDummy085] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy000))).fv) 0

theorem nb056_fresh_021 :
    (nb056AlphaDummy086) ∉ (((Class.cv (nb056AlphaDummy000))).fv) := by
  simpa only [nb056AlphaDummy086] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy000))).fv) 1

theorem nb056_distinct_022 : (nb056AlphaDummy085) ≠ (nb056AlphaDummy086) := by
  simpa only [nb056AlphaDummy085, nb056AlphaDummy086] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy000))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_023 :
    (nb056AlphaDummy005) ∉
      (((Class.cv (nb056AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) :=
  by
  simpa only [nb056AlphaDummy005] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv)
      0

theorem nb056_fresh_024 :
    (nb056AlphaDummy006) ∉
      (((Class.cv (nb056AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) :=
  by
  simpa only [nb056AlphaDummy006] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv)
      1

theorem nb056_fresh_025 :
    (nb056AlphaDummy007) ∉
      (((Class.cv (nb056AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) :=
  by
  simpa only [nb056AlphaDummy007] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv)
      2

theorem nb056_distinct_026 : (nb056AlphaDummy005) ≠ (nb056AlphaDummy006) := by
  simpa only [nb056AlphaDummy005, nb056AlphaDummy006] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_distinct_027 : (nb056AlphaDummy005) ≠ (nb056AlphaDummy007) := by
  simpa only [nb056AlphaDummy005, nb056AlphaDummy007] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) (i := 0) (j := 2) (by decide))

theorem nb056_distinct_028 : (nb056AlphaDummy006) ≠ (nb056AlphaDummy007) := by
  simpa only [nb056AlphaDummy006, nb056AlphaDummy007] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) (i := 1) (j := 2) (by decide))

theorem nb056_fresh_029 :
    (nb056AlphaDummy013) ∉
      (((Class.cv (nb056AlphaDummy005))).fv ∪ ((Class.cv (nb056AlphaDummy006))).fv) :=
  by
  simpa only [nb056AlphaDummy013] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy005))).fv ∪ ((Class.cv (nb056AlphaDummy006))).fv)
      0

theorem nb056_fresh_030 :
    (nb056AlphaDummy014) ∉
      (((Class.cv (nb056AlphaDummy005))).fv ∪ ((Class.cv (nb056AlphaDummy006))).fv) :=
  by
  simpa only [nb056AlphaDummy014] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy005))).fv ∪ ((Class.cv (nb056AlphaDummy006))).fv)
      1

theorem nb056_distinct_031 : (nb056AlphaDummy013) ≠ (nb056AlphaDummy014) := by
  simpa only [nb056AlphaDummy013, nb056AlphaDummy014] using
    (freshVar_injective
      (((Class.cv (nb056AlphaDummy005))).fv ∪ ((Class.cv (nb056AlphaDummy006))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb056_fresh_032 :
    (nb056AlphaDummy049) ∉
      (((Class.cv (nb056AlphaDummy005))).fv ∪ ((Class.cv (nb056AlphaDummy007))).fv) :=
  by
  simpa only [nb056AlphaDummy049] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy005))).fv ∪ ((Class.cv (nb056AlphaDummy007))).fv)
      0

theorem nb056_fresh_033 :
    (nb056AlphaDummy050) ∉
      (((Class.cv (nb056AlphaDummy005))).fv ∪ ((Class.cv (nb056AlphaDummy007))).fv) :=
  by
  simpa only [nb056AlphaDummy050] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy005))).fv ∪ ((Class.cv (nb056AlphaDummy007))).fv)
      1

theorem nb056_distinct_034 : (nb056AlphaDummy049) ≠ (nb056AlphaDummy050) := by
  simpa only [nb056AlphaDummy049, nb056AlphaDummy050] using
    (freshVar_injective
      (((Class.cv (nb056AlphaDummy005))).fv ∪ ((Class.cv (nb056AlphaDummy007))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb056_fresh_035 :
    (nb056AlphaDummy163) ∉
      (((Class.cv (nb056AlphaDummy007))).fv ∪ ((Class.cv (nb056AlphaDummy006))).fv) :=
  by
  simpa only [nb056AlphaDummy163] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy007))).fv ∪ ((Class.cv (nb056AlphaDummy006))).fv)
      0

theorem nb056_fresh_036 :
    (nb056AlphaDummy164) ∉
      (((Class.cv (nb056AlphaDummy007))).fv ∪ ((Class.cv (nb056AlphaDummy006))).fv) :=
  by
  simpa only [nb056AlphaDummy164] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy007))).fv ∪ ((Class.cv (nb056AlphaDummy006))).fv)
      1

theorem nb056_distinct_037 : (nb056AlphaDummy163) ≠ (nb056AlphaDummy164) := by
  simpa only [nb056AlphaDummy163, nb056AlphaDummy164] using
    (freshVar_injective
      (((Class.cv (nb056AlphaDummy007))).fv ∪ ((Class.cv (nb056AlphaDummy006))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb056_fresh_038 (f : Var) :
    (nb056AlphaDummy015 f) ∉
      (((Class.cv (nb056AlphaDummy008 f))).fv ∪ ((Class.cv (nb056AlphaDummy009 f))).fv) :=
  by
  simpa only [nb056AlphaDummy015] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy008 f))).fv ∪ ((Class.cv (nb056AlphaDummy009 f))).fv)
      0

theorem nb056_fresh_039 (f : Var) :
    (nb056AlphaDummy016 f) ∉
      (((Class.cv (nb056AlphaDummy008 f))).fv ∪ ((Class.cv (nb056AlphaDummy009 f))).fv) :=
  by
  simpa only [nb056AlphaDummy016] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy008 f))).fv ∪ ((Class.cv (nb056AlphaDummy009 f))).fv)
      1

theorem nb056_distinct_040 (f : Var) :
    (nb056AlphaDummy015 f) ≠ (nb056AlphaDummy016 f) := by
  simpa only [nb056AlphaDummy015, nb056AlphaDummy016] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy008 f))).fv ∪
        ((Class.cv (nb056AlphaDummy009 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_041 (f : Var) :
    (nb056AlphaDummy051 f) ∉
      (((Class.cv (nb056AlphaDummy008 f))).fv ∪ ((Class.cv (nb056AlphaDummy010 f))).fv) :=
  by
  simpa only [nb056AlphaDummy051] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy008 f))).fv ∪ ((Class.cv (nb056AlphaDummy010 f))).fv)
      0

theorem nb056_fresh_042 (f : Var) :
    (nb056AlphaDummy052 f) ∉
      (((Class.cv (nb056AlphaDummy008 f))).fv ∪ ((Class.cv (nb056AlphaDummy010 f))).fv) :=
  by
  simpa only [nb056AlphaDummy052] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy008 f))).fv ∪ ((Class.cv (nb056AlphaDummy010 f))).fv)
      1

theorem nb056_distinct_043 (f : Var) :
    (nb056AlphaDummy051 f) ≠ (nb056AlphaDummy052 f) := by
  simpa only [nb056AlphaDummy051, nb056AlphaDummy052] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy008 f))).fv ∪
        ((Class.cv (nb056AlphaDummy010 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_044 (f : Var) :
    (nb056AlphaDummy165 f) ∉
      (((Class.cv (nb056AlphaDummy010 f))).fv ∪ ((Class.cv (nb056AlphaDummy009 f))).fv) :=
  by
  simpa only [nb056AlphaDummy165] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy010 f))).fv ∪ ((Class.cv (nb056AlphaDummy009 f))).fv)
      0

theorem nb056_fresh_045 (f : Var) :
    (nb056AlphaDummy166 f) ∉
      (((Class.cv (nb056AlphaDummy010 f))).fv ∪ ((Class.cv (nb056AlphaDummy009 f))).fv) :=
  by
  simpa only [nb056AlphaDummy166] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy010 f))).fv ∪ ((Class.cv (nb056AlphaDummy009 f))).fv)
      1

theorem nb056_distinct_046 (f : Var) :
    (nb056AlphaDummy165 f) ≠ (nb056AlphaDummy166 f) := by
  simpa only [nb056AlphaDummy165, nb056AlphaDummy166] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy010 f))).fv ∪
        ((Class.cv (nb056AlphaDummy009 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_047 :
    (nb056AlphaDummy021) ∉ (((Class.cv (nb056AlphaDummy014))).fv) := by
  simpa only [nb056AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy014))).fv) 0

theorem nb056_fresh_048 :
    (nb056AlphaDummy022) ∉ (((Class.cv (nb056AlphaDummy014))).fv) := by
  simpa only [nb056AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy014))).fv) 1

theorem nb056_distinct_049 : (nb056AlphaDummy021) ≠ (nb056AlphaDummy022) := by
  simpa only [nb056AlphaDummy021, nb056AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy014))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_050 (f : Var) :
    (nb056AlphaDummy023 f) ∉ (((Class.cv (nb056AlphaDummy016 f))).fv) := by
  simpa only [nb056AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy016 f))).fv) 0

theorem nb056_fresh_051 (f : Var) :
    (nb056AlphaDummy024 f) ∉ (((Class.cv (nb056AlphaDummy016 f))).fv) := by
  simpa only [nb056AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy016 f))).fv) 1

theorem nb056_distinct_052 (f : Var) :
    (nb056AlphaDummy023 f) ≠ (nb056AlphaDummy024 f) := by
  simpa only [nb056AlphaDummy023, nb056AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy016 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb056_fresh_053 :
    (nb056AlphaDummy027) ∉
      (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy027] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv) 0

theorem nb056_fresh_054 :
    (nb056AlphaDummy028) ∉
      (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy028] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv) 1

theorem nb056_fresh_055 :
    (nb056AlphaDummy029) ∉
      (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy029] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv) 2

theorem nb056_distinct_056 : (nb056AlphaDummy027) ≠ (nb056AlphaDummy028) := by
  simpa only [nb056AlphaDummy027, nb056AlphaDummy028] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb056_distinct_057 : (nb056AlphaDummy027) ≠ (nb056AlphaDummy029) := by
  simpa only [nb056AlphaDummy027, nb056AlphaDummy029] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb056_distinct_058 : (nb056AlphaDummy028) ≠ (nb056AlphaDummy029) := by
  simpa only [nb056AlphaDummy028, nb056AlphaDummy029] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb056_fresh_059 (f : Var) :
    (nb056AlphaDummy030 f) ∉
      (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy030] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv) 0

theorem nb056_fresh_060 (f : Var) :
    (nb056AlphaDummy031 f) ∉
      (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy031] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv) 1

theorem nb056_fresh_061 (f : Var) :
    (nb056AlphaDummy032 f) ∉
      (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy032] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv) 2

theorem nb056_distinct_062 (f : Var) :
    (nb056AlphaDummy030 f) ≠ (nb056AlphaDummy031 f) := by
  simpa only [nb056AlphaDummy030, nb056AlphaDummy031] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb056_distinct_063 (f : Var) :
    (nb056AlphaDummy030 f) ≠ (nb056AlphaDummy032 f) := by
  simpa only [nb056AlphaDummy030, nb056AlphaDummy032] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb056_distinct_064 (f : Var) :
    (nb056AlphaDummy031 f) ≠ (nb056AlphaDummy032 f) := by
  simpa only [nb056AlphaDummy031, nb056AlphaDummy032] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb056_fresh_065 :
    (nb056AlphaDummy039) ∉
      (((Class.cv (nb056AlphaDummy028))).fv ∪ ((Class.cv (nb056AlphaDummy028))).fv) :=
  by
  simpa only [nb056AlphaDummy039] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy028))).fv ∪ ((Class.cv (nb056AlphaDummy028))).fv)
      0

theorem nb056_fresh_066 :
    (nb056AlphaDummy035) ∉
      (((Class.cv (nb056AlphaDummy028))).fv ∪ ((Class.cv (nb056AlphaDummy029))).fv) :=
  by
  simpa only [nb056AlphaDummy035] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy028))).fv ∪ ((Class.cv (nb056AlphaDummy029))).fv)
      0

theorem nb056_fresh_067 :
    (nb056AlphaDummy041) ∉
      (((Class.cv (nb056AlphaDummy029))).fv ∪ ((Class.cv (nb056AlphaDummy029))).fv) :=
  by
  simpa only [nb056AlphaDummy041] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy029))).fv ∪ ((Class.cv (nb056AlphaDummy029))).fv)
      0

theorem nb056_fresh_068 (f : Var) :
    (nb056AlphaDummy040 f) ∉
      (((Class.cv (nb056AlphaDummy031 f))).fv ∪ ((Class.cv (nb056AlphaDummy031 f))).fv) :=
  by
  simpa only [nb056AlphaDummy040] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy031 f))).fv ∪ ((Class.cv (nb056AlphaDummy031 f))).fv)
      0

theorem nb056_fresh_069 (f : Var) :
    (nb056AlphaDummy036 f) ∉
      (((Class.cv (nb056AlphaDummy031 f))).fv ∪ ((Class.cv (nb056AlphaDummy032 f))).fv) :=
  by
  simpa only [nb056AlphaDummy036] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy031 f))).fv ∪ ((Class.cv (nb056AlphaDummy032 f))).fv)
      0

theorem nb056_fresh_070 (f : Var) :
    (nb056AlphaDummy042 f) ∉
      (((Class.cv (nb056AlphaDummy032 f))).fv ∪ ((Class.cv (nb056AlphaDummy032 f))).fv) :=
  by
  simpa only [nb056AlphaDummy042] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy032 f))).fv ∪ ((Class.cv (nb056AlphaDummy032 f))).fv)
      0

theorem nb056_fresh_071 :
    (nb056AlphaDummy057) ∉ (((Class.cv (nb056AlphaDummy050))).fv) := by
  simpa only [nb056AlphaDummy057] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy050))).fv) 0

theorem nb056_fresh_072 :
    (nb056AlphaDummy058) ∉ (((Class.cv (nb056AlphaDummy050))).fv) := by
  simpa only [nb056AlphaDummy058] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy050))).fv) 1

theorem nb056_distinct_073 : (nb056AlphaDummy057) ≠ (nb056AlphaDummy058) := by
  simpa only [nb056AlphaDummy057, nb056AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy050))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_074 (f : Var) :
    (nb056AlphaDummy059 f) ∉ (((Class.cv (nb056AlphaDummy052 f))).fv) := by
  simpa only [nb056AlphaDummy059] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy052 f))).fv) 0

theorem nb056_fresh_075 (f : Var) :
    (nb056AlphaDummy060 f) ∉ (((Class.cv (nb056AlphaDummy052 f))).fv) := by
  simpa only [nb056AlphaDummy060] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy052 f))).fv) 1

theorem nb056_distinct_076 (f : Var) :
    (nb056AlphaDummy059 f) ≠ (nb056AlphaDummy060 f) := by
  simpa only [nb056AlphaDummy059, nb056AlphaDummy060] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy052 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb056_fresh_077 :
    (nb056AlphaDummy063) ∉
      (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy063] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv) 0

theorem nb056_fresh_078 :
    (nb056AlphaDummy064) ∉
      (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy064] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv) 1

theorem nb056_fresh_079 :
    (nb056AlphaDummy065) ∉
      (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy065] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv) 2

theorem nb056_distinct_080 : (nb056AlphaDummy063) ≠ (nb056AlphaDummy064) := by
  simpa only [nb056AlphaDummy063, nb056AlphaDummy064] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb056_distinct_081 : (nb056AlphaDummy063) ≠ (nb056AlphaDummy065) := by
  simpa only [nb056AlphaDummy063, nb056AlphaDummy065] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb056_distinct_082 : (nb056AlphaDummy064) ≠ (nb056AlphaDummy065) := by
  simpa only [nb056AlphaDummy064, nb056AlphaDummy065] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb056_fresh_083 (f : Var) :
    (nb056AlphaDummy066 f) ∉
      (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy066] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv) 0

theorem nb056_fresh_084 (f : Var) :
    (nb056AlphaDummy067 f) ∉
      (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy067] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv) 1

theorem nb056_fresh_085 (f : Var) :
    (nb056AlphaDummy068 f) ∉
      (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy068] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv) 2

theorem nb056_distinct_086 (f : Var) :
    (nb056AlphaDummy066 f) ≠ (nb056AlphaDummy067 f) := by
  simpa only [nb056AlphaDummy066, nb056AlphaDummy067] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb056_distinct_087 (f : Var) :
    (nb056AlphaDummy066 f) ≠ (nb056AlphaDummy068 f) := by
  simpa only [nb056AlphaDummy066, nb056AlphaDummy068] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb056_distinct_088 (f : Var) :
    (nb056AlphaDummy067 f) ≠ (nb056AlphaDummy068 f) := by
  simpa only [nb056AlphaDummy067, nb056AlphaDummy068] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb056_fresh_089 :
    (nb056AlphaDummy075) ∉
      (((Class.cv (nb056AlphaDummy064))).fv ∪ ((Class.cv (nb056AlphaDummy064))).fv) :=
  by
  simpa only [nb056AlphaDummy075] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy064))).fv ∪ ((Class.cv (nb056AlphaDummy064))).fv)
      0

theorem nb056_fresh_090 :
    (nb056AlphaDummy071) ∉
      (((Class.cv (nb056AlphaDummy064))).fv ∪ ((Class.cv (nb056AlphaDummy065))).fv) :=
  by
  simpa only [nb056AlphaDummy071] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy064))).fv ∪ ((Class.cv (nb056AlphaDummy065))).fv)
      0

theorem nb056_fresh_091 :
    (nb056AlphaDummy077) ∉
      (((Class.cv (nb056AlphaDummy065))).fv ∪ ((Class.cv (nb056AlphaDummy065))).fv) :=
  by
  simpa only [nb056AlphaDummy077] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy065))).fv ∪ ((Class.cv (nb056AlphaDummy065))).fv)
      0

theorem nb056_fresh_092 (f : Var) :
    (nb056AlphaDummy076 f) ∉
      (((Class.cv (nb056AlphaDummy067 f))).fv ∪ ((Class.cv (nb056AlphaDummy067 f))).fv) :=
  by
  simpa only [nb056AlphaDummy076] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy067 f))).fv ∪ ((Class.cv (nb056AlphaDummy067 f))).fv)
      0

theorem nb056_fresh_093 (f : Var) :
    (nb056AlphaDummy072 f) ∉
      (((Class.cv (nb056AlphaDummy067 f))).fv ∪ ((Class.cv (nb056AlphaDummy068 f))).fv) :=
  by
  simpa only [nb056AlphaDummy072] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy067 f))).fv ∪ ((Class.cv (nb056AlphaDummy068 f))).fv)
      0

theorem nb056_fresh_094 (f : Var) :
    (nb056AlphaDummy078 f) ∉
      (((Class.cv (nb056AlphaDummy068 f))).fv ∪ ((Class.cv (nb056AlphaDummy068 f))).fv) :=
  by
  simpa only [nb056AlphaDummy078] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy068 f))).fv ∪ ((Class.cv (nb056AlphaDummy068 f))).fv)
      0

theorem nb056_fresh_095 :
    (nb056AlphaDummy091) ∉
      (((Class.cv (nb056AlphaDummy085))).fv ∪ ((Class.cv (nb056AlphaDummy086))).fv) :=
  by
  simpa only [nb056AlphaDummy091] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy085))).fv ∪ ((Class.cv (nb056AlphaDummy086))).fv)
      0

theorem nb056_fresh_096 :
    (nb056AlphaDummy092) ∉
      (((Class.cv (nb056AlphaDummy085))).fv ∪ ((Class.cv (nb056AlphaDummy086))).fv) :=
  by
  simpa only [nb056AlphaDummy092] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy085))).fv ∪ ((Class.cv (nb056AlphaDummy086))).fv)
      1

theorem nb056_distinct_097 : (nb056AlphaDummy091) ≠ (nb056AlphaDummy092) := by
  simpa only [nb056AlphaDummy091, nb056AlphaDummy092] using
    (freshVar_injective
      (((Class.cv (nb056AlphaDummy085))).fv ∪ ((Class.cv (nb056AlphaDummy086))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb056_fresh_098 :
    (nb056AlphaDummy127) ∉
      (((Class.cv (nb056AlphaDummy086))).fv ∪ ((Class.cv (nb056AlphaDummy085))).fv) :=
  by
  simpa only [nb056AlphaDummy127] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy086))).fv ∪ ((Class.cv (nb056AlphaDummy085))).fv)
      0

theorem nb056_fresh_099 :
    (nb056AlphaDummy128) ∉
      (((Class.cv (nb056AlphaDummy086))).fv ∪ ((Class.cv (nb056AlphaDummy085))).fv) :=
  by
  simpa only [nb056AlphaDummy128] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy086))).fv ∪ ((Class.cv (nb056AlphaDummy085))).fv)
      1

theorem nb056_distinct_100 : (nb056AlphaDummy127) ≠ (nb056AlphaDummy128) := by
  simpa only [nb056AlphaDummy127, nb056AlphaDummy128] using
    (freshVar_injective
      (((Class.cv (nb056AlphaDummy086))).fv ∪ ((Class.cv (nb056AlphaDummy085))).fv)
      (i := 0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C056C001Part003`. -/


section

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

theorem nb056_fresh_101 (f : Var) :
    (nb056AlphaDummy093 f) ∉
      (((Class.cv (nb056AlphaDummy087 f))).fv ∪ ((Class.cv (nb056AlphaDummy088 f))).fv) :=
  by
  simpa only [nb056AlphaDummy093] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy087 f))).fv ∪ ((Class.cv (nb056AlphaDummy088 f))).fv)
      0

theorem nb056_fresh_102 (f : Var) :
    (nb056AlphaDummy094 f) ∉
      (((Class.cv (nb056AlphaDummy087 f))).fv ∪ ((Class.cv (nb056AlphaDummy088 f))).fv) :=
  by
  simpa only [nb056AlphaDummy094] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy087 f))).fv ∪ ((Class.cv (nb056AlphaDummy088 f))).fv)
      1

theorem nb056_distinct_103 (f : Var) :
    (nb056AlphaDummy093 f) ≠ (nb056AlphaDummy094 f) := by
  simpa only [nb056AlphaDummy093, nb056AlphaDummy094] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy087 f))).fv ∪
        ((Class.cv (nb056AlphaDummy088 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_104 (f : Var) :
    (nb056AlphaDummy129 f) ∉
      (((Class.cv (nb056AlphaDummy088 f))).fv ∪ ((Class.cv (nb056AlphaDummy087 f))).fv) :=
  by
  simpa only [nb056AlphaDummy129] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy088 f))).fv ∪ ((Class.cv (nb056AlphaDummy087 f))).fv)
      0

theorem nb056_fresh_105 (f : Var) :
    (nb056AlphaDummy130 f) ∉
      (((Class.cv (nb056AlphaDummy088 f))).fv ∪ ((Class.cv (nb056AlphaDummy087 f))).fv) :=
  by
  simpa only [nb056AlphaDummy130] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy088 f))).fv ∪ ((Class.cv (nb056AlphaDummy087 f))).fv)
      1

theorem nb056_distinct_106 (f : Var) :
    (nb056AlphaDummy129 f) ≠ (nb056AlphaDummy130 f) := by
  simpa only [nb056AlphaDummy129, nb056AlphaDummy130] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy088 f))).fv ∪
        ((Class.cv (nb056AlphaDummy087 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_107 :
    (nb056AlphaDummy099) ∉ (((Class.cv (nb056AlphaDummy092))).fv) := by
  simpa only [nb056AlphaDummy099] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy092))).fv) 0

theorem nb056_fresh_108 :
    (nb056AlphaDummy100) ∉ (((Class.cv (nb056AlphaDummy092))).fv) := by
  simpa only [nb056AlphaDummy100] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy092))).fv) 1

theorem nb056_distinct_109 : (nb056AlphaDummy099) ≠ (nb056AlphaDummy100) := by
  simpa only [nb056AlphaDummy099, nb056AlphaDummy100] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy092))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_110 (f : Var) :
    (nb056AlphaDummy101 f) ∉ (((Class.cv (nb056AlphaDummy094 f))).fv) := by
  simpa only [nb056AlphaDummy101] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy094 f))).fv) 0

theorem nb056_fresh_111 (f : Var) :
    (nb056AlphaDummy102 f) ∉ (((Class.cv (nb056AlphaDummy094 f))).fv) := by
  simpa only [nb056AlphaDummy102] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy094 f))).fv) 1

theorem nb056_distinct_112 (f : Var) :
    (nb056AlphaDummy101 f) ≠ (nb056AlphaDummy102 f) := by
  simpa only [nb056AlphaDummy101, nb056AlphaDummy102] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy094 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb056_fresh_113 :
    (nb056AlphaDummy105) ∉
      (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy105] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv) 0

theorem nb056_fresh_114 :
    (nb056AlphaDummy106) ∉
      (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy106] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv) 1

theorem nb056_fresh_115 :
    (nb056AlphaDummy107) ∉
      (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy107] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv) 2

theorem nb056_distinct_116 : (nb056AlphaDummy105) ≠ (nb056AlphaDummy106) := by
  simpa only [nb056AlphaDummy105, nb056AlphaDummy106] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb056_distinct_117 : (nb056AlphaDummy105) ≠ (nb056AlphaDummy107) := by
  simpa only [nb056AlphaDummy105, nb056AlphaDummy107] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb056_distinct_118 : (nb056AlphaDummy106) ≠ (nb056AlphaDummy107) := by
  simpa only [nb056AlphaDummy106, nb056AlphaDummy107] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb056_fresh_119 (f : Var) :
    (nb056AlphaDummy108 f) ∉
      (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy108] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv) 0

theorem nb056_fresh_120 (f : Var) :
    (nb056AlphaDummy109 f) ∉
      (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy109] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv) 1

theorem nb056_fresh_121 (f : Var) :
    (nb056AlphaDummy110 f) ∉
      (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy110] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv) 2

theorem nb056_distinct_122 (f : Var) :
    (nb056AlphaDummy108 f) ≠ (nb056AlphaDummy109 f) := by
  simpa only [nb056AlphaDummy108, nb056AlphaDummy109] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb056_distinct_123 (f : Var) :
    (nb056AlphaDummy108 f) ≠ (nb056AlphaDummy110 f) := by
  simpa only [nb056AlphaDummy108, nb056AlphaDummy110] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb056_distinct_124 (f : Var) :
    (nb056AlphaDummy109 f) ≠ (nb056AlphaDummy110 f) := by
  simpa only [nb056AlphaDummy109, nb056AlphaDummy110] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb056_fresh_125 :
    (nb056AlphaDummy117) ∉
      (((Class.cv (nb056AlphaDummy106))).fv ∪ ((Class.cv (nb056AlphaDummy106))).fv) :=
  by
  simpa only [nb056AlphaDummy117] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy106))).fv ∪ ((Class.cv (nb056AlphaDummy106))).fv)
      0

theorem nb056_fresh_126 :
    (nb056AlphaDummy113) ∉
      (((Class.cv (nb056AlphaDummy106))).fv ∪ ((Class.cv (nb056AlphaDummy107))).fv) :=
  by
  simpa only [nb056AlphaDummy113] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy106))).fv ∪ ((Class.cv (nb056AlphaDummy107))).fv)
      0

theorem nb056_fresh_127 :
    (nb056AlphaDummy119) ∉
      (((Class.cv (nb056AlphaDummy107))).fv ∪ ((Class.cv (nb056AlphaDummy107))).fv) :=
  by
  simpa only [nb056AlphaDummy119] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy107))).fv ∪ ((Class.cv (nb056AlphaDummy107))).fv)
      0

theorem nb056_fresh_128 (f : Var) :
    (nb056AlphaDummy118 f) ∉
      (((Class.cv (nb056AlphaDummy109 f))).fv ∪ ((Class.cv (nb056AlphaDummy109 f))).fv) :=
  by
  simpa only [nb056AlphaDummy118] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy109 f))).fv ∪ ((Class.cv (nb056AlphaDummy109 f))).fv)
      0

theorem nb056_fresh_129 (f : Var) :
    (nb056AlphaDummy114 f) ∉
      (((Class.cv (nb056AlphaDummy109 f))).fv ∪ ((Class.cv (nb056AlphaDummy110 f))).fv) :=
  by
  simpa only [nb056AlphaDummy114] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy109 f))).fv ∪ ((Class.cv (nb056AlphaDummy110 f))).fv)
      0

theorem nb056_fresh_130 (f : Var) :
    (nb056AlphaDummy120 f) ∉
      (((Class.cv (nb056AlphaDummy110 f))).fv ∪ ((Class.cv (nb056AlphaDummy110 f))).fv) :=
  by
  simpa only [nb056AlphaDummy120] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy110 f))).fv ∪ ((Class.cv (nb056AlphaDummy110 f))).fv)
      0

theorem nb056_fresh_131 :
    (nb056AlphaDummy135) ∉ (((Class.cv (nb056AlphaDummy128))).fv) := by
  simpa only [nb056AlphaDummy135] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy128))).fv) 0

theorem nb056_fresh_132 :
    (nb056AlphaDummy136) ∉ (((Class.cv (nb056AlphaDummy128))).fv) := by
  simpa only [nb056AlphaDummy136] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy128))).fv) 1

theorem nb056_distinct_133 : (nb056AlphaDummy135) ≠ (nb056AlphaDummy136) := by
  simpa only [nb056AlphaDummy135, nb056AlphaDummy136] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy128))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_134 (f : Var) :
    (nb056AlphaDummy137 f) ∉ (((Class.cv (nb056AlphaDummy130 f))).fv) := by
  simpa only [nb056AlphaDummy137] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy130 f))).fv) 0

theorem nb056_fresh_135 (f : Var) :
    (nb056AlphaDummy138 f) ∉ (((Class.cv (nb056AlphaDummy130 f))).fv) := by
  simpa only [nb056AlphaDummy138] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy130 f))).fv) 1

theorem nb056_distinct_136 (f : Var) :
    (nb056AlphaDummy137 f) ≠ (nb056AlphaDummy138 f) := by
  simpa only [nb056AlphaDummy137, nb056AlphaDummy138] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy130 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb056_fresh_137 :
    (nb056AlphaDummy141) ∉
      (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy141] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv) 0

theorem nb056_fresh_138 :
    (nb056AlphaDummy142) ∉
      (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy142] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv) 1

theorem nb056_fresh_139 :
    (nb056AlphaDummy143) ∉
      (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy143] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv) 2

theorem nb056_distinct_140 : (nb056AlphaDummy141) ≠ (nb056AlphaDummy142) := by
  simpa only [nb056AlphaDummy141, nb056AlphaDummy142] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb056_distinct_141 : (nb056AlphaDummy141) ≠ (nb056AlphaDummy143) := by
  simpa only [nb056AlphaDummy141, nb056AlphaDummy143] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb056_distinct_142 : (nb056AlphaDummy142) ≠ (nb056AlphaDummy143) := by
  simpa only [nb056AlphaDummy142, nb056AlphaDummy143] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb056_fresh_143 (f : Var) :
    (nb056AlphaDummy144 f) ∉
      (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy144] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv) 0

theorem nb056_fresh_144 (f : Var) :
    (nb056AlphaDummy145 f) ∉
      (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy145] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv) 1

theorem nb056_fresh_145 (f : Var) :
    (nb056AlphaDummy146 f) ∉
      (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy146] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv) 2

theorem nb056_distinct_146 (f : Var) :
    (nb056AlphaDummy144 f) ≠ (nb056AlphaDummy145 f) := by
  simpa only [nb056AlphaDummy144, nb056AlphaDummy145] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb056_distinct_147 (f : Var) :
    (nb056AlphaDummy144 f) ≠ (nb056AlphaDummy146 f) := by
  simpa only [nb056AlphaDummy144, nb056AlphaDummy146] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb056_distinct_148 (f : Var) :
    (nb056AlphaDummy145 f) ≠ (nb056AlphaDummy146 f) := by
  simpa only [nb056AlphaDummy145, nb056AlphaDummy146] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb056_fresh_149 :
    (nb056AlphaDummy153) ∉
      (((Class.cv (nb056AlphaDummy142))).fv ∪ ((Class.cv (nb056AlphaDummy142))).fv) :=
  by
  simpa only [nb056AlphaDummy153] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy142))).fv ∪ ((Class.cv (nb056AlphaDummy142))).fv)
      0

theorem nb056_fresh_150 :
    (nb056AlphaDummy149) ∉
      (((Class.cv (nb056AlphaDummy142))).fv ∪ ((Class.cv (nb056AlphaDummy143))).fv) :=
  by
  simpa only [nb056AlphaDummy149] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy142))).fv ∪ ((Class.cv (nb056AlphaDummy143))).fv)
      0

theorem nb056_fresh_151 :
    (nb056AlphaDummy155) ∉
      (((Class.cv (nb056AlphaDummy143))).fv ∪ ((Class.cv (nb056AlphaDummy143))).fv) :=
  by
  simpa only [nb056AlphaDummy155] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy143))).fv ∪ ((Class.cv (nb056AlphaDummy143))).fv)
      0

theorem nb056_fresh_152 (f : Var) :
    (nb056AlphaDummy154 f) ∉
      (((Class.cv (nb056AlphaDummy145 f))).fv ∪ ((Class.cv (nb056AlphaDummy145 f))).fv) :=
  by
  simpa only [nb056AlphaDummy154] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy145 f))).fv ∪ ((Class.cv (nb056AlphaDummy145 f))).fv)
      0

theorem nb056_fresh_153 (f : Var) :
    (nb056AlphaDummy150 f) ∉
      (((Class.cv (nb056AlphaDummy145 f))).fv ∪ ((Class.cv (nb056AlphaDummy146 f))).fv) :=
  by
  simpa only [nb056AlphaDummy150] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy145 f))).fv ∪ ((Class.cv (nb056AlphaDummy146 f))).fv)
      0

theorem nb056_fresh_154 (f : Var) :
    (nb056AlphaDummy156 f) ∉
      (((Class.cv (nb056AlphaDummy146 f))).fv ∪ ((Class.cv (nb056AlphaDummy146 f))).fv) :=
  by
  simpa only [nb056AlphaDummy156] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy146 f))).fv ∪ ((Class.cv (nb056AlphaDummy146 f))).fv)
      0

theorem nb056_fresh_155 :
    (nb056AlphaDummy171) ∉ (((Class.cv (nb056AlphaDummy164))).fv) := by
  simpa only [nb056AlphaDummy171] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy164))).fv) 0

theorem nb056_fresh_156 :
    (nb056AlphaDummy172) ∉ (((Class.cv (nb056AlphaDummy164))).fv) := by
  simpa only [nb056AlphaDummy172] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy164))).fv) 1

theorem nb056_distinct_157 : (nb056AlphaDummy171) ≠ (nb056AlphaDummy172) := by
  simpa only [nb056AlphaDummy171, nb056AlphaDummy172] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy164))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_158 (f : Var) :
    (nb056AlphaDummy173 f) ∉ (((Class.cv (nb056AlphaDummy166 f))).fv) := by
  simpa only [nb056AlphaDummy173] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy166 f))).fv) 0

theorem nb056_fresh_159 (f : Var) :
    (nb056AlphaDummy174 f) ∉ (((Class.cv (nb056AlphaDummy166 f))).fv) := by
  simpa only [nb056AlphaDummy174] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy166 f))).fv) 1

theorem nb056_distinct_160 (f : Var) :
    (nb056AlphaDummy173 f) ≠ (nb056AlphaDummy174 f) := by
  simpa only [nb056AlphaDummy173, nb056AlphaDummy174] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy166 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb056_fresh_161 :
    (nb056AlphaDummy177) ∉
      (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy177] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv) 0

theorem nb056_fresh_162 :
    (nb056AlphaDummy178) ∉
      (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy178] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv) 1

theorem nb056_fresh_163 :
    (nb056AlphaDummy179) ∉
      (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy179] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv) 2

theorem nb056_distinct_164 : (nb056AlphaDummy177) ≠ (nb056AlphaDummy178) := by
  simpa only [nb056AlphaDummy177, nb056AlphaDummy178] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb056_distinct_165 : (nb056AlphaDummy177) ≠ (nb056AlphaDummy179) := by
  simpa only [nb056AlphaDummy177, nb056AlphaDummy179] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb056_distinct_166 : (nb056AlphaDummy178) ≠ (nb056AlphaDummy179) := by
  simpa only [nb056AlphaDummy178, nb056AlphaDummy179] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb056_fresh_167 (f : Var) :
    (nb056AlphaDummy180 f) ∉
      (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy180] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv) 0

theorem nb056_fresh_168 (f : Var) :
    (nb056AlphaDummy181 f) ∉
      (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy181] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv) 1

theorem nb056_fresh_169 (f : Var) :
    (nb056AlphaDummy182 f) ∉
      (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb056AlphaDummy182] using
    freshVar_not_mem (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv) 2

theorem nb056_distinct_170 (f : Var) :
    (nb056AlphaDummy180 f) ≠ (nb056AlphaDummy181 f) := by
  simpa only [nb056AlphaDummy180, nb056AlphaDummy181] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb056_distinct_171 (f : Var) :
    (nb056AlphaDummy180 f) ≠ (nb056AlphaDummy182 f) := by
  simpa only [nb056AlphaDummy180, nb056AlphaDummy182] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb056_distinct_172 (f : Var) :
    (nb056AlphaDummy181 f) ≠ (nb056AlphaDummy182 f) := by
  simpa only [nb056AlphaDummy181, nb056AlphaDummy182] using
    (freshVar_injective (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb056_fresh_173 :
    (nb056AlphaDummy189) ∉
      (((Class.cv (nb056AlphaDummy178))).fv ∪ ((Class.cv (nb056AlphaDummy178))).fv) :=
  by
  simpa only [nb056AlphaDummy189] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy178))).fv ∪ ((Class.cv (nb056AlphaDummy178))).fv)
      0

theorem nb056_fresh_174 :
    (nb056AlphaDummy185) ∉
      (((Class.cv (nb056AlphaDummy178))).fv ∪ ((Class.cv (nb056AlphaDummy179))).fv) :=
  by
  simpa only [nb056AlphaDummy185] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy178))).fv ∪ ((Class.cv (nb056AlphaDummy179))).fv)
      0

theorem nb056_fresh_175 :
    (nb056AlphaDummy191) ∉
      (((Class.cv (nb056AlphaDummy179))).fv ∪ ((Class.cv (nb056AlphaDummy179))).fv) :=
  by
  simpa only [nb056AlphaDummy191] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy179))).fv ∪ ((Class.cv (nb056AlphaDummy179))).fv)
      0

theorem nb056_fresh_176 (f : Var) :
    (nb056AlphaDummy190 f) ∉
      (((Class.cv (nb056AlphaDummy181 f))).fv ∪ ((Class.cv (nb056AlphaDummy181 f))).fv) :=
  by
  simpa only [nb056AlphaDummy190] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy181 f))).fv ∪ ((Class.cv (nb056AlphaDummy181 f))).fv)
      0

theorem nb056_fresh_177 (f : Var) :
    (nb056AlphaDummy186 f) ∉
      (((Class.cv (nb056AlphaDummy181 f))).fv ∪ ((Class.cv (nb056AlphaDummy182 f))).fv) :=
  by
  simpa only [nb056AlphaDummy186] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy181 f))).fv ∪ ((Class.cv (nb056AlphaDummy182 f))).fv)
      0

theorem nb056_fresh_178 (f : Var) :
    (nb056AlphaDummy192 f) ∉
      (((Class.cv (nb056AlphaDummy182 f))).fv ∪ ((Class.cv (nb056AlphaDummy182 f))).fv) :=
  by
  simpa only [nb056AlphaDummy192] using
    freshVar_not_mem
      (((Class.cv (nb056AlphaDummy182 f))).fv ∪ ((Class.cv (nb056AlphaDummy182 f))).fv)
      0

theorem nb056_fresh_179 (f : Var) : (nb056AlphaDummy087 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb056AlphaDummy087] using freshVar_not_mem (((Class.cv f)).fv) 0

theorem nb056_fresh_180 (f : Var) : (nb056AlphaDummy088 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb056AlphaDummy088] using freshVar_not_mem (((Class.cv f)).fv) 1

theorem nb056_distinct_181 (f : Var) :
    (nb056AlphaDummy087 f) ≠ (nb056AlphaDummy088 f) := by
  simpa only [nb056AlphaDummy087, nb056AlphaDummy088] using
    (freshVar_injective (((Class.cv f)).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_182 (f : Var) :
    (nb056AlphaDummy008 f) ∉ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) := by
  simpa only [nb056AlphaDummy008] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 0

theorem nb056_fresh_183 (f : Var) :
    (nb056AlphaDummy009 f) ∉ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) := by
  simpa only [nb056AlphaDummy009] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 1

theorem nb056_fresh_184 (f : Var) :
    (nb056AlphaDummy010 f) ∉ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) := by
  simpa only [nb056AlphaDummy010] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 2

theorem nb056_distinct_185 (f : Var) :
    (nb056AlphaDummy008 f) ≠ (nb056AlphaDummy009 f) := by
  simpa only [nb056AlphaDummy008, nb056AlphaDummy009] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb056_distinct_186 (f : Var) :
    (nb056AlphaDummy008 f) ≠ (nb056AlphaDummy010 f) := by
  simpa only [nb056AlphaDummy008, nb056AlphaDummy010] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (i := 0) (j :=
      2) (by decide))

theorem nb056_distinct_187 (f : Var) :
    (nb056AlphaDummy009 f) ≠ (nb056AlphaDummy010 f) := by
  simpa only [nb056AlphaDummy009, nb056AlphaDummy010] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (i := 1) (j :=
      2) (by decide))

theorem nb056_fresh_188 :
    (nb056AlphaDummy025) ∉
      (((Wff.classMem (Class.cv (nb056AlphaDummy021)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy021)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy021))).fv) :=
  by
  simpa only [nb056AlphaDummy025] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb056AlphaDummy021)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy021)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy021))).fv)
      0

theorem nb056_fresh_189 (f : Var) :
    (nb056AlphaDummy026 f) ∉
      (((Wff.classMem (Class.cv (nb056AlphaDummy023 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy023 f)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy023 f))).fv) :=
  by
  simpa only [nb056AlphaDummy026] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb056AlphaDummy023 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy023 f)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy023 f))).fv)
      0

theorem nb056_fresh_190 :
    (nb056AlphaDummy061) ∉
      (((Wff.classMem (Class.cv (nb056AlphaDummy057)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy057)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy057))).fv) :=
  by
  simpa only [nb056AlphaDummy061] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb056AlphaDummy057)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy057)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy057))).fv)
      0

theorem nb056_fresh_191 (f : Var) :
    (nb056AlphaDummy062 f) ∉
      (((Wff.classMem (Class.cv (nb056AlphaDummy059 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy059 f)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy059 f))).fv) :=
  by
  simpa only [nb056AlphaDummy062] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb056AlphaDummy059 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy059 f)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy059 f))).fv)
      0

theorem nb056_fresh_192 :
    (nb056AlphaDummy103) ∉
      (((Wff.classMem (Class.cv (nb056AlphaDummy099)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy099)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy099))).fv) :=
  by
  simpa only [nb056AlphaDummy103] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb056AlphaDummy099)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy099)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy099))).fv)
      0

theorem nb056_fresh_193 (f : Var) :
    (nb056AlphaDummy104 f) ∉
      (((Wff.classMem (Class.cv (nb056AlphaDummy101 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy101 f)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy101 f))).fv) :=
  by
  simpa only [nb056AlphaDummy104] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb056AlphaDummy101 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy101 f)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy101 f))).fv)
      0

theorem nb056_fresh_194 :
    (nb056AlphaDummy139) ∉
      (((Wff.classMem (Class.cv (nb056AlphaDummy135)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy135)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy135))).fv) :=
  by
  simpa only [nb056AlphaDummy139] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb056AlphaDummy135)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy135)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy135))).fv)
      0

theorem nb056_fresh_195 (f : Var) :
    (nb056AlphaDummy140 f) ∉
      (((Wff.classMem (Class.cv (nb056AlphaDummy137 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy137 f)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy137 f))).fv) :=
  by
  simpa only [nb056AlphaDummy140] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb056AlphaDummy137 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy137 f)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy137 f))).fv)
      0

theorem nb056_fresh_196 :
    (nb056AlphaDummy175) ∉
      (((Wff.classMem (Class.cv (nb056AlphaDummy171)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy171)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy171))).fv) :=
  by
  simpa only [nb056AlphaDummy175] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb056AlphaDummy171)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy171)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy171))).fv)
      0

theorem nb056_fresh_197 (f : Var) :
    (nb056AlphaDummy176 f) ∉
      (((Wff.classMem (Class.cv (nb056AlphaDummy173 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy173 f)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy173 f))).fv) :=
  by
  simpa only [nb056AlphaDummy176] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb056AlphaDummy173 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy173 f)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy173 f))).fv)
      0

theorem nb056_fresh_198 :
    (nb056AlphaDummy003) ∉
      (((synCcom (Class.cv (nb056AlphaDummy000))
            (synCcnv (Class.cv (nb056AlphaDummy000))))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb056AlphaDummy003] using
    freshVar_not_mem
      (((synCcom (Class.cv (nb056AlphaDummy000))
            (synCcnv (Class.cv (nb056AlphaDummy000))))).fv ∪ ((synCid)).fv)
      0

theorem nb056_fresh_199 (f : Var) :
    (nb056AlphaDummy004 f) ∉
      (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb056AlphaDummy004] using
    freshVar_not_mem
      (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) 0

theorem nb056_fresh_200 :
    (nb056AlphaDummy017) ∉
      (((synCcompl (Class.cab (nb056AlphaDummy013)
              (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy005))
                (Wff.classEq (Class.cv (nb056AlphaDummy013))
                  (synCphi (Class.cv (nb056AlphaDummy014)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy013)
              (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy006))
                (Wff.classEq (Class.cv (nb056AlphaDummy013))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy014)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb056AlphaDummy017] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb056AlphaDummy013)
              (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy005))
                (Wff.classEq (Class.cv (nb056AlphaDummy013))
                  (synCphi (Class.cv (nb056AlphaDummy014)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy013)
              (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy006))
                (Wff.classEq (Class.cv (nb056AlphaDummy013))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy014)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb056_fresh_201 (f : Var) :
    (nb056AlphaDummy018 f) ∉
      (((synCcompl (Class.cab (nb056AlphaDummy015 f)
              (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy008 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                  (synCphi (Class.cv (nb056AlphaDummy016 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy015 f)
              (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy009 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy016 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb056AlphaDummy018] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb056AlphaDummy015 f)
              (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy008 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                  (synCphi (Class.cv (nb056AlphaDummy016 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy015 f)
              (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy009 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy016 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb056_fresh_202 :
    (nb056AlphaDummy053) ∉
      (((synCcompl (Class.cab (nb056AlphaDummy049)
              (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy005))
                (Wff.classEq (Class.cv (nb056AlphaDummy049))
                  (synCphi (Class.cv (nb056AlphaDummy050)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy049)
              (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy007))
                (Wff.classEq (Class.cv (nb056AlphaDummy049))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy050)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb056AlphaDummy053] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb056AlphaDummy049)
              (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy005))
                (Wff.classEq (Class.cv (nb056AlphaDummy049))
                  (synCphi (Class.cv (nb056AlphaDummy050)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy049)
              (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy007))
                (Wff.classEq (Class.cv (nb056AlphaDummy049))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy050)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb056_fresh_203 (f : Var) :
    (nb056AlphaDummy054 f) ∉
      (((synCcompl (Class.cab (nb056AlphaDummy051 f)
              (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy008 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                  (synCphi (Class.cv (nb056AlphaDummy052 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy051 f)
              (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy010 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy052 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb056AlphaDummy054] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb056AlphaDummy051 f)
              (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy008 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                  (synCphi (Class.cv (nb056AlphaDummy052 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy051 f)
              (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy010 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy052 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb056_fresh_204 :
    (nb056AlphaDummy095) ∉
      (((synCcompl (Class.cab (nb056AlphaDummy091)
              (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy085))
                (Wff.classEq (Class.cv (nb056AlphaDummy091))
                  (synCphi (Class.cv (nb056AlphaDummy092)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy091)
              (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy086))
                (Wff.classEq (Class.cv (nb056AlphaDummy091))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy092)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb056AlphaDummy095] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb056AlphaDummy091)
              (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy085))
                (Wff.classEq (Class.cv (nb056AlphaDummy091))
                  (synCphi (Class.cv (nb056AlphaDummy092)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy091)
              (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy086))
                (Wff.classEq (Class.cv (nb056AlphaDummy091))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy092)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb056_fresh_205 (f : Var) :
    (nb056AlphaDummy096 f) ∉
      (((synCcompl (Class.cab (nb056AlphaDummy093 f)
              (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy087 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                  (synCphi (Class.cv (nb056AlphaDummy094 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy093 f)
              (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy088 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy094 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb056AlphaDummy096] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb056AlphaDummy093 f)
              (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy087 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                  (synCphi (Class.cv (nb056AlphaDummy094 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy093 f)
              (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy088 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy094 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb056_fresh_206 :
    (nb056AlphaDummy131) ∉
      (((synCcompl (Class.cab (nb056AlphaDummy127)
              (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy086))
                (Wff.classEq (Class.cv (nb056AlphaDummy127))
                  (synCphi (Class.cv (nb056AlphaDummy128)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy127)
              (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy085))
                (Wff.classEq (Class.cv (nb056AlphaDummy127))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy128)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb056AlphaDummy131] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb056AlphaDummy127)
              (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy086))
                (Wff.classEq (Class.cv (nb056AlphaDummy127))
                  (synCphi (Class.cv (nb056AlphaDummy128)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy127)
              (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy085))
                (Wff.classEq (Class.cv (nb056AlphaDummy127))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy128)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb056_fresh_207 (f : Var) :
    (nb056AlphaDummy132 f) ∉
      (((synCcompl (Class.cab (nb056AlphaDummy129 f)
              (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy088 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                  (synCphi (Class.cv (nb056AlphaDummy130 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy129 f)
              (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy087 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy130 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb056AlphaDummy132] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb056AlphaDummy129 f)
              (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy088 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                  (synCphi (Class.cv (nb056AlphaDummy130 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy129 f)
              (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy087 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy130 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb056_fresh_208 :
    (nb056AlphaDummy167) ∉
      (((synCcompl (Class.cab (nb056AlphaDummy163)
              (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy007))
                (Wff.classEq (Class.cv (nb056AlphaDummy163))
                  (synCphi (Class.cv (nb056AlphaDummy164)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy163)
              (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy006))
                (Wff.classEq (Class.cv (nb056AlphaDummy163))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy164)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb056AlphaDummy167] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb056AlphaDummy163)
              (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy007))
                (Wff.classEq (Class.cv (nb056AlphaDummy163))
                  (synCphi (Class.cv (nb056AlphaDummy164)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy163)
              (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy006))
                (Wff.classEq (Class.cv (nb056AlphaDummy163))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy164)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb056_fresh_209 (f : Var) :
    (nb056AlphaDummy168 f) ∉
      (((synCcompl (Class.cab (nb056AlphaDummy165 f)
              (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy010 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                  (synCphi (Class.cv (nb056AlphaDummy166 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy165 f)
              (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy009 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy166 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb056AlphaDummy168] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb056AlphaDummy165 f)
              (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy010 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                  (synCphi (Class.cv (nb056AlphaDummy166 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy165 f)
              (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy009 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy166 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb056_fresh_210 :
    (nb056AlphaDummy037) ∉
      (((synCcompl (Class.cv (nb056AlphaDummy028)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy029)))).fv) :=
  by
  simpa only [nb056AlphaDummy037] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb056AlphaDummy028)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy029)))).fv)
      0

theorem nb056_fresh_211 (f : Var) :
    (nb056AlphaDummy038 f) ∉
      (((synCcompl (Class.cv (nb056AlphaDummy031 f)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy032 f)))).fv) :=
  by
  simpa only [nb056AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb056AlphaDummy031 f)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy032 f)))).fv)
      0

theorem nb056_fresh_212 :
    (nb056AlphaDummy073) ∉
      (((synCcompl (Class.cv (nb056AlphaDummy064)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy065)))).fv) :=
  by
  simpa only [nb056AlphaDummy073] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb056AlphaDummy064)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy065)))).fv)
      0

theorem nb056_fresh_213 (f : Var) :
    (nb056AlphaDummy074 f) ∉
      (((synCcompl (Class.cv (nb056AlphaDummy067 f)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy068 f)))).fv) :=
  by
  simpa only [nb056AlphaDummy074] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb056AlphaDummy067 f)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy068 f)))).fv)
      0

theorem nb056_fresh_214 :
    (nb056AlphaDummy115) ∉
      (((synCcompl (Class.cv (nb056AlphaDummy106)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy107)))).fv) :=
  by
  simpa only [nb056AlphaDummy115] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb056AlphaDummy106)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy107)))).fv)
      0

theorem nb056_fresh_215 (f : Var) :
    (nb056AlphaDummy116 f) ∉
      (((synCcompl (Class.cv (nb056AlphaDummy109 f)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy110 f)))).fv) :=
  by
  simpa only [nb056AlphaDummy116] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb056AlphaDummy109 f)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy110 f)))).fv)
      0

theorem nb056_fresh_216 :
    (nb056AlphaDummy151) ∉
      (((synCcompl (Class.cv (nb056AlphaDummy142)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy143)))).fv) :=
  by
  simpa only [nb056AlphaDummy151] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb056AlphaDummy142)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy143)))).fv)
      0

theorem nb056_fresh_217 (f : Var) :
    (nb056AlphaDummy152 f) ∉
      (((synCcompl (Class.cv (nb056AlphaDummy145 f)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy146 f)))).fv) :=
  by
  simpa only [nb056AlphaDummy152] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb056AlphaDummy145 f)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy146 f)))).fv)
      0

theorem nb056_fresh_218 :
    (nb056AlphaDummy187) ∉
      (((synCcompl (Class.cv (nb056AlphaDummy178)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy179)))).fv) :=
  by
  simpa only [nb056AlphaDummy187] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb056AlphaDummy178)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy179)))).fv)
      0

theorem nb056_fresh_219 (f : Var) :
    (nb056AlphaDummy188 f) ∉
      (((synCcompl (Class.cv (nb056AlphaDummy181 f)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy182 f)))).fv) :=
  by
  simpa only [nb056AlphaDummy188] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb056AlphaDummy181 f)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy182 f)))).fv)
      0

theorem nb056_fresh_220 :
    (nb056AlphaDummy045) ∉
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy014))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb056AlphaDummy045] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy014))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb056_fresh_221 (f : Var) :
    (nb056AlphaDummy046 f) ∉
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy016 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb056AlphaDummy046] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy016 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb056_fresh_222 :
    (nb056AlphaDummy081) ∉
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy050))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb056AlphaDummy081] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy050))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb056_fresh_223 (f : Var) :
    (nb056AlphaDummy082 f) ∉
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy052 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb056AlphaDummy082] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy052 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb056_fresh_224 :
    (nb056AlphaDummy123) ∉
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy092))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb056AlphaDummy123] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy092))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb056_fresh_225 (f : Var) :
    (nb056AlphaDummy124 f) ∉
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy094 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb056AlphaDummy124] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy094 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb056_fresh_226 :
    (nb056AlphaDummy159) ∉
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy128))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb056AlphaDummy159] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy128))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb056_fresh_227 (f : Var) :
    (nb056AlphaDummy160 f) ∉
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy130 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb056AlphaDummy160] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy130 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb056_fresh_228 :
    (nb056AlphaDummy195) ∉
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy164))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb056AlphaDummy195] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy164))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb056_fresh_229 (f : Var) :
    (nb056AlphaDummy196 f) ∉
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy166 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb056AlphaDummy196] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy166 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb056_fresh_230 :
    (nb056AlphaDummy033) ∉
      (((synCnin (Class.cv (nb056AlphaDummy028)) (Class.cv (nb056AlphaDummy029)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy028))
            (Class.cv (nb056AlphaDummy029)))).fv) :=
  by
  simpa only [nb056AlphaDummy033] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb056AlphaDummy028)) (Class.cv (nb056AlphaDummy029)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy028)) (Class.cv (nb056AlphaDummy029)))).fv)
      0

theorem nb056_fresh_231 (f : Var) :
    (nb056AlphaDummy034 f) ∉
      (((synCnin (Class.cv (nb056AlphaDummy031 f))
            (Class.cv (nb056AlphaDummy032 f)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy031 f))
            (Class.cv (nb056AlphaDummy032 f)))).fv) :=
  by
  simpa only [nb056AlphaDummy034] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb056AlphaDummy031 f))
            (Class.cv (nb056AlphaDummy032 f)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy031 f))
            (Class.cv (nb056AlphaDummy032 f)))).fv)
      0

theorem nb056_fresh_232 :
    (nb056AlphaDummy069) ∉
      (((synCnin (Class.cv (nb056AlphaDummy064)) (Class.cv (nb056AlphaDummy065)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy064))
            (Class.cv (nb056AlphaDummy065)))).fv) :=
  by
  simpa only [nb056AlphaDummy069] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb056AlphaDummy064)) (Class.cv (nb056AlphaDummy065)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy064)) (Class.cv (nb056AlphaDummy065)))).fv)
      0

theorem nb056_fresh_233 (f : Var) :
    (nb056AlphaDummy070 f) ∉
      (((synCnin (Class.cv (nb056AlphaDummy067 f))
            (Class.cv (nb056AlphaDummy068 f)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy067 f))
            (Class.cv (nb056AlphaDummy068 f)))).fv) :=
  by
  simpa only [nb056AlphaDummy070] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb056AlphaDummy067 f))
            (Class.cv (nb056AlphaDummy068 f)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy067 f))
            (Class.cv (nb056AlphaDummy068 f)))).fv)
      0

theorem nb056_fresh_234 :
    (nb056AlphaDummy111) ∉
      (((synCnin (Class.cv (nb056AlphaDummy106)) (Class.cv (nb056AlphaDummy107)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy106))
            (Class.cv (nb056AlphaDummy107)))).fv) :=
  by
  simpa only [nb056AlphaDummy111] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb056AlphaDummy106)) (Class.cv (nb056AlphaDummy107)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy106)) (Class.cv (nb056AlphaDummy107)))).fv)
      0

theorem nb056_fresh_235 (f : Var) :
    (nb056AlphaDummy112 f) ∉
      (((synCnin (Class.cv (nb056AlphaDummy109 f))
            (Class.cv (nb056AlphaDummy110 f)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy109 f))
            (Class.cv (nb056AlphaDummy110 f)))).fv) :=
  by
  simpa only [nb056AlphaDummy112] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb056AlphaDummy109 f))
            (Class.cv (nb056AlphaDummy110 f)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy109 f))
            (Class.cv (nb056AlphaDummy110 f)))).fv)
      0

theorem nb056_fresh_236 :
    (nb056AlphaDummy147) ∉
      (((synCnin (Class.cv (nb056AlphaDummy142)) (Class.cv (nb056AlphaDummy143)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy142))
            (Class.cv (nb056AlphaDummy143)))).fv) :=
  by
  simpa only [nb056AlphaDummy147] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb056AlphaDummy142)) (Class.cv (nb056AlphaDummy143)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy142)) (Class.cv (nb056AlphaDummy143)))).fv)
      0

theorem nb056_fresh_237 (f : Var) :
    (nb056AlphaDummy148 f) ∉
      (((synCnin (Class.cv (nb056AlphaDummy145 f))
            (Class.cv (nb056AlphaDummy146 f)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy145 f))
            (Class.cv (nb056AlphaDummy146 f)))).fv) :=
  by
  simpa only [nb056AlphaDummy148] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb056AlphaDummy145 f))
            (Class.cv (nb056AlphaDummy146 f)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy145 f))
            (Class.cv (nb056AlphaDummy146 f)))).fv)
      0

theorem nb056_fresh_238 :
    (nb056AlphaDummy183) ∉
      (((synCnin (Class.cv (nb056AlphaDummy178)) (Class.cv (nb056AlphaDummy179)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy178))
            (Class.cv (nb056AlphaDummy179)))).fv) :=
  by
  simpa only [nb056AlphaDummy183] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb056AlphaDummy178)) (Class.cv (nb056AlphaDummy179)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy178)) (Class.cv (nb056AlphaDummy179)))).fv)
      0

theorem nb056_fresh_239 (f : Var) :
    (nb056AlphaDummy184 f) ∉
      (((synCnin (Class.cv (nb056AlphaDummy181 f))
            (Class.cv (nb056AlphaDummy182 f)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy181 f))
            (Class.cv (nb056AlphaDummy182 f)))).fv) :=
  by
  simpa only [nb056AlphaDummy184] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb056AlphaDummy181 f))
            (Class.cv (nb056AlphaDummy182 f)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy181 f))
            (Class.cv (nb056AlphaDummy182 f)))).fv)
      0

theorem nb056_fresh_240 :
    (nb056AlphaDummy001) ∉
      (((synCnin (synCcom (Class.cv (nb056AlphaDummy000))
              (synCcnv (Class.cv (nb056AlphaDummy000)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb056AlphaDummy000))
              (synCcnv (Class.cv (nb056AlphaDummy000)))) (synCid))).fv) :=
  by
  simpa only [nb056AlphaDummy001] using
    freshVar_not_mem
      (((synCnin (synCcom (Class.cv (nb056AlphaDummy000))
              (synCcnv (Class.cv (nb056AlphaDummy000)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb056AlphaDummy000))
              (synCcnv (Class.cv (nb056AlphaDummy000)))) (synCid))).fv)
      0

theorem nb056_fresh_241 (f : Var) :
    (nb056AlphaDummy002 f) ∉
      (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv) :=
  by
  simpa only [nb056AlphaDummy002] using
    freshVar_not_mem
      (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv)
      0

theorem nb056_fresh_242 :
    (nb056AlphaDummy047) ∉
      (((synCphi (Class.cv (nb056AlphaDummy014)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy014)))).fv) :=
  by
  simpa only [nb056AlphaDummy047] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb056AlphaDummy014)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy014)))).fv)
      0

theorem nb056_fresh_243 (f : Var) :
    (nb056AlphaDummy048 f) ∉
      (((synCphi (Class.cv (nb056AlphaDummy016 f)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy016 f)))).fv) :=
  by
  simpa only [nb056AlphaDummy048] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb056AlphaDummy016 f)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy016 f)))).fv)
      0

theorem nb056_fresh_244 :
    (nb056AlphaDummy083) ∉
      (((synCphi (Class.cv (nb056AlphaDummy050)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy050)))).fv) :=
  by
  simpa only [nb056AlphaDummy083] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb056AlphaDummy050)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy050)))).fv)
      0

theorem nb056_fresh_245 (f : Var) :
    (nb056AlphaDummy084 f) ∉
      (((synCphi (Class.cv (nb056AlphaDummy052 f)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy052 f)))).fv) :=
  by
  simpa only [nb056AlphaDummy084] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb056AlphaDummy052 f)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy052 f)))).fv)
      0

theorem nb056_fresh_246 :
    (nb056AlphaDummy125) ∉
      (((synCphi (Class.cv (nb056AlphaDummy092)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy092)))).fv) :=
  by
  simpa only [nb056AlphaDummy125] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb056AlphaDummy092)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy092)))).fv)
      0

theorem nb056_fresh_247 (f : Var) :
    (nb056AlphaDummy126 f) ∉
      (((synCphi (Class.cv (nb056AlphaDummy094 f)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy094 f)))).fv) :=
  by
  simpa only [nb056AlphaDummy126] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb056AlphaDummy094 f)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy094 f)))).fv)
      0

theorem nb056_fresh_248 :
    (nb056AlphaDummy161) ∉
      (((synCphi (Class.cv (nb056AlphaDummy128)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy128)))).fv) :=
  by
  simpa only [nb056AlphaDummy161] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb056AlphaDummy128)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy128)))).fv)
      0

theorem nb056_fresh_249 (f : Var) :
    (nb056AlphaDummy162 f) ∉
      (((synCphi (Class.cv (nb056AlphaDummy130 f)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy130 f)))).fv) :=
  by
  simpa only [nb056AlphaDummy162] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb056AlphaDummy130 f)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy130 f)))).fv)
      0

theorem nb056_fresh_250 :
    (nb056AlphaDummy197) ∉
      (((synCphi (Class.cv (nb056AlphaDummy164)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy164)))).fv) :=
  by
  simpa only [nb056AlphaDummy197] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb056AlphaDummy164)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy164)))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C056C001Part004`. -/


section

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

theorem nb056_fresh_251 (f : Var) :
    (nb056AlphaDummy198 f) ∉
      (((synCphi (Class.cv (nb056AlphaDummy166 f)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy166 f)))).fv) :=
  by
  simpa only [nb056AlphaDummy198] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb056AlphaDummy166 f)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy166 f)))).fv)
      0

theorem nb056_fresh_252 :
    (nb056AlphaDummy011) ∉
      (({(nb056AlphaDummy005)} : Finset Var) ∪ ({(nb056AlphaDummy006)} : Finset Var) ∪
        ((synWex (nb056AlphaDummy007) (synWa (synWbr (Class.cv (nb056AlphaDummy005))
                (synCcnv (Class.cv (nb056AlphaDummy000)))
                (Class.cv (nb056AlphaDummy007))) (synWbr (Class.cv (nb056AlphaDummy007))
                (Class.cv (nb056AlphaDummy000)) (Class.cv (nb056AlphaDummy006)))))).fv) :=
  by
  simpa only [nb056AlphaDummy011] using
    freshVar_not_mem
      (({(nb056AlphaDummy005)} : Finset Var) ∪ ({(nb056AlphaDummy006)} : Finset Var) ∪
        ((synWex (nb056AlphaDummy007) (synWa (synWbr (Class.cv (nb056AlphaDummy005))
                (synCcnv (Class.cv (nb056AlphaDummy000)))
                (Class.cv (nb056AlphaDummy007))) (synWbr (Class.cv (nb056AlphaDummy007))
                (Class.cv (nb056AlphaDummy000)) (Class.cv (nb056AlphaDummy006)))))).fv)
      0

theorem nb056_fresh_253 (f : Var) :
    (nb056AlphaDummy012 f) ∉
      (({(nb056AlphaDummy008 f)} : Finset Var) ∪ ({(nb056AlphaDummy009 f)} : Finset Var) ∪
        ((synWex (nb056AlphaDummy010 f) (synWa
              (synWbr (Class.cv (nb056AlphaDummy008 f)) (synCcnv (Class.cv f))
                (Class.cv (nb056AlphaDummy010 f)))
              (synWbr (Class.cv (nb056AlphaDummy010 f)) (Class.cv f)
                (Class.cv (nb056AlphaDummy009 f)))))).fv) :=
  by
  simpa only [nb056AlphaDummy012] using
    freshVar_not_mem
      (({(nb056AlphaDummy008 f)} : Finset Var) ∪ ({(nb056AlphaDummy009 f)} : Finset Var) ∪
        ((synWex (nb056AlphaDummy010 f) (synWa
              (synWbr (Class.cv (nb056AlphaDummy008 f)) (synCcnv (Class.cv f))
                (Class.cv (nb056AlphaDummy010 f)))
              (synWbr (Class.cv (nb056AlphaDummy010 f)) (Class.cv f)
                (Class.cv (nb056AlphaDummy009 f)))))).fv)
      0

theorem nb056_fresh_254 :
    (nb056AlphaDummy089) ∉
      (({(nb056AlphaDummy085)} : Finset Var) ∪ ({(nb056AlphaDummy086)} : Finset Var) ∪
        ((synWbr (Class.cv (nb056AlphaDummy086)) (Class.cv (nb056AlphaDummy000))
            (Class.cv (nb056AlphaDummy085)))).fv) :=
  by
  simpa only [nb056AlphaDummy089] using
    freshVar_not_mem
      (({(nb056AlphaDummy085)} : Finset Var) ∪ ({(nb056AlphaDummy086)} : Finset Var) ∪
        ((synWbr (Class.cv (nb056AlphaDummy086)) (Class.cv (nb056AlphaDummy000))
            (Class.cv (nb056AlphaDummy085)))).fv)
      0

theorem nb056_fresh_255 (f : Var) :
    (nb056AlphaDummy090 f) ∉
      (({(nb056AlphaDummy087 f)} : Finset Var) ∪ ({(nb056AlphaDummy088 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb056AlphaDummy088 f)) (Class.cv f)
            (Class.cv (nb056AlphaDummy087 f)))).fv) :=
  by
  simpa only [nb056AlphaDummy090] using
    freshVar_not_mem
      (({(nb056AlphaDummy087 f)} : Finset Var) ∪ ({(nb056AlphaDummy088 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb056AlphaDummy088 f)) (Class.cv f)
            (Class.cv (nb056AlphaDummy087 f)))).fv)
      0

theorem nb056_fresh_256 : (nb056AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb056AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb056_support_mem_0000 :
    (nb056AlphaDummy005) ∈
      (({(nb056AlphaDummy005)} : Finset Var) ∪ ({(nb056AlphaDummy006)} : Finset Var) ∪
        ((synWex (nb056AlphaDummy007) (synWa (synWbr (Class.cv (nb056AlphaDummy005))
                (synCcnv (Class.cv (nb056AlphaDummy000)))
                (Class.cv (nb056AlphaDummy007))) (synWbr (Class.cv (nb056AlphaDummy007))
                (Class.cv (nb056AlphaDummy000)) (Class.cv (nb056AlphaDummy006)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0001 (f : Var) :
    (nb056AlphaDummy008 f) ∈
      (({(nb056AlphaDummy008 f)} : Finset Var) ∪ ({(nb056AlphaDummy009 f)} : Finset Var) ∪
        ((synWex (nb056AlphaDummy010 f) (synWa
              (synWbr (Class.cv (nb056AlphaDummy008 f)) (synCcnv (Class.cv f))
                (Class.cv (nb056AlphaDummy010 f)))
              (synWbr (Class.cv (nb056AlphaDummy010 f)) (Class.cv f)
                (Class.cv (nb056AlphaDummy009 f)))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := (nb056AlphaDummy008 f)) (s :=
        ({(nb056AlphaDummy008 f)} : Finset Var) ∪ ({(nb056AlphaDummy009 f)} : Finset Var))
        ((synWex (nb056AlphaDummy010 f) (synWa
              (synWbr (Class.cv (nb056AlphaDummy008 f)) (synCcnv (Class.cv f))
                (Class.cv (nb056AlphaDummy010 f)))
              (synWbr (Class.cv (nb056AlphaDummy010 f)) (Class.cv f)
                (Class.cv (nb056AlphaDummy009 f)))))).fv
        ?_
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0002 :
    (nb056AlphaDummy006) ∈
      (({(nb056AlphaDummy005)} : Finset Var) ∪ ({(nb056AlphaDummy006)} : Finset Var) ∪
        ((synWex (nb056AlphaDummy007) (synWa (synWbr (Class.cv (nb056AlphaDummy005))
                (synCcnv (Class.cv (nb056AlphaDummy000)))
                (Class.cv (nb056AlphaDummy007))) (synWbr (Class.cv (nb056AlphaDummy007))
                (Class.cv (nb056AlphaDummy000)) (Class.cv (nb056AlphaDummy006)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0003 (f : Var) :
    (nb056AlphaDummy009 f) ∈
      (({(nb056AlphaDummy008 f)} : Finset Var) ∪ ({(nb056AlphaDummy009 f)} : Finset Var) ∪
        ((synWex (nb056AlphaDummy010 f) (synWa
              (synWbr (Class.cv (nb056AlphaDummy008 f)) (synCcnv (Class.cv f))
                (Class.cv (nb056AlphaDummy010 f)))
              (synWbr (Class.cv (nb056AlphaDummy010 f)) (Class.cv f)
                (Class.cv (nb056AlphaDummy009 f)))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := (nb056AlphaDummy009 f)) (s :=
        ({(nb056AlphaDummy008 f)} : Finset Var) ∪ ({(nb056AlphaDummy009 f)} : Finset Var))
        ((synWex (nb056AlphaDummy010 f) (synWa
              (synWbr (Class.cv (nb056AlphaDummy008 f)) (synCcnv (Class.cv f))
                (Class.cv (nb056AlphaDummy010 f)))
              (synWbr (Class.cv (nb056AlphaDummy010 f)) (Class.cv f)
                (Class.cv (nb056AlphaDummy009 f)))))).fv
        ?_
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0004 :
    (nb056AlphaDummy005) ∈
      (((Class.cv (nb056AlphaDummy005))).fv ∪ ((Class.cv (nb056AlphaDummy006))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0005 :
    (nb056AlphaDummy005) ∈
      (((synCcompl (Class.cab (nb056AlphaDummy013)
              (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy005))
                (Wff.classEq (Class.cv (nb056AlphaDummy013))
                  (synCphi (Class.cv (nb056AlphaDummy014)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy013)
              (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy006))
                (Wff.classEq (Class.cv (nb056AlphaDummy013))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy014)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0006 (f : Var) :
    (nb056AlphaDummy008 f) ∈
      (((Class.cv (nb056AlphaDummy008 f))).fv ∪ ((Class.cv (nb056AlphaDummy009 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0007 (f : Var) :
    (nb056AlphaDummy008 f) ∈
      (((synCcompl (Class.cab (nb056AlphaDummy015 f)
              (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy008 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                  (synCphi (Class.cv (nb056AlphaDummy016 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy015 f)
              (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy009 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy016 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0006 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0006 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0008 :
    (nb056AlphaDummy005) ∈
      (((Class.cab (nb056AlphaDummy013)
            (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy005))
              (Wff.classEq (Class.cv (nb056AlphaDummy013))
                (synCphi (Class.cv (nb056AlphaDummy014))))))).fv ∪
        ((Class.cab (nb056AlphaDummy013)
            (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy005))
              (Wff.classEq (Class.cv (nb056AlphaDummy013))
                (synCphi (Class.cv (nb056AlphaDummy014))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0009 (f : Var) :
    (nb056AlphaDummy008 f) ∈
      (((Class.cab (nb056AlphaDummy015 f)
            (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy008 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                (synCphi (Class.cv (nb056AlphaDummy016 f))))))).fv ∪
        ((Class.cab (nb056AlphaDummy015 f)
            (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy008 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                (synCphi (Class.cv (nb056AlphaDummy016 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0006 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0006 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0010 :
    (nb056AlphaDummy014) ∈ (((Class.cv (nb056AlphaDummy014))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0011 (f : Var) :
    (nb056AlphaDummy016 f) ∈ (((Class.cv (nb056AlphaDummy016 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0012 :
    (nb056AlphaDummy021) ∈
      (((Wff.classMem (Class.cv (nb056AlphaDummy021)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy021)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy021))).fv) :=
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

theorem nb056_support_mem_0013 (f : Var) :
    (nb056AlphaDummy023 f) ∈
      (((Wff.classMem (Class.cv (nb056AlphaDummy023 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy023 f)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy023 f))).fv) :=
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

theorem nb056_support_mem_0014 :
    (nb056AlphaDummy021) ∈
      (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0015 (f : Var) :
    (nb056AlphaDummy023 f) ∈
      (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0016 :
    (nb056AlphaDummy028) ∈
      (((synCnin (Class.cv (nb056AlphaDummy028)) (Class.cv (nb056AlphaDummy029)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy028))
            (Class.cv (nb056AlphaDummy029)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0017 (f : Var) :
    (nb056AlphaDummy031 f) ∈
      (((synCnin (Class.cv (nb056AlphaDummy031 f))
            (Class.cv (nb056AlphaDummy032 f)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy031 f))
            (Class.cv (nb056AlphaDummy032 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0018 :
    (nb056AlphaDummy028) ∈
      (((Class.cv (nb056AlphaDummy028))).fv ∪ ((Class.cv (nb056AlphaDummy029))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0019 (f : Var) :
    (nb056AlphaDummy031 f) ∈
      (((Class.cv (nb056AlphaDummy031 f))).fv ∪ ((Class.cv (nb056AlphaDummy032 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0020 :
    (nb056AlphaDummy029) ∈
      (((synCnin (Class.cv (nb056AlphaDummy028)) (Class.cv (nb056AlphaDummy029)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy028))
            (Class.cv (nb056AlphaDummy029)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0021 (f : Var) :
    (nb056AlphaDummy032 f) ∈
      (((synCnin (Class.cv (nb056AlphaDummy031 f))
            (Class.cv (nb056AlphaDummy032 f)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy031 f))
            (Class.cv (nb056AlphaDummy032 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0022 :
    (nb056AlphaDummy029) ∈
      (((Class.cv (nb056AlphaDummy028))).fv ∪ ((Class.cv (nb056AlphaDummy029))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0023 (f : Var) :
    (nb056AlphaDummy032 f) ∈
      (((Class.cv (nb056AlphaDummy031 f))).fv ∪ ((Class.cv (nb056AlphaDummy032 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0024 :
    (nb056AlphaDummy028) ∈
      (((synCcompl (Class.cv (nb056AlphaDummy028)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy029)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0025 (f : Var) :
    (nb056AlphaDummy031 f) ∈
      (((synCcompl (Class.cv (nb056AlphaDummy031 f)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy032 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0026 :
    (nb056AlphaDummy028) ∈
      (((Class.cv (nb056AlphaDummy028))).fv ∪ ((Class.cv (nb056AlphaDummy028))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0027 (f : Var) :
    (nb056AlphaDummy031 f) ∈
      (((Class.cv (nb056AlphaDummy031 f))).fv ∪ ((Class.cv (nb056AlphaDummy031 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0028 :
    (nb056AlphaDummy029) ∈
      (((synCcompl (Class.cv (nb056AlphaDummy028)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy029)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0029 (f : Var) :
    (nb056AlphaDummy032 f) ∈
      (((synCcompl (Class.cv (nb056AlphaDummy031 f)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy032 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0030 :
    (nb056AlphaDummy029) ∈
      (((Class.cv (nb056AlphaDummy029))).fv ∪ ((Class.cv (nb056AlphaDummy029))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0031 (f : Var) :
    (nb056AlphaDummy032 f) ∈
      (((Class.cv (nb056AlphaDummy032 f))).fv ∪ ((Class.cv (nb056AlphaDummy032 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0032 :
    (nb056AlphaDummy006) ∈
      (((Class.cv (nb056AlphaDummy005))).fv ∪ ((Class.cv (nb056AlphaDummy006))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0033 :
    (nb056AlphaDummy006) ∈
      (((synCcompl (Class.cab (nb056AlphaDummy013)
              (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy005))
                (Wff.classEq (Class.cv (nb056AlphaDummy013))
                  (synCphi (Class.cv (nb056AlphaDummy014)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy013)
              (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy006))
                (Wff.classEq (Class.cv (nb056AlphaDummy013))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy014)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0034 (f : Var) :
    (nb056AlphaDummy009 f) ∈
      (((Class.cv (nb056AlphaDummy008 f))).fv ∪ ((Class.cv (nb056AlphaDummy009 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0035 (f : Var) :
    (nb056AlphaDummy009 f) ∈
      (((synCcompl (Class.cab (nb056AlphaDummy015 f)
              (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy008 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                  (synCphi (Class.cv (nb056AlphaDummy016 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy015 f)
              (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy009 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy016 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0036 :
    (nb056AlphaDummy006) ∈
      (((Class.cab (nb056AlphaDummy013)
            (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy006))
              (Wff.classEq (Class.cv (nb056AlphaDummy013))
                (synCun (synCphi (Class.cv (nb056AlphaDummy014)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy013)
            (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy006))
              (Wff.classEq (Class.cv (nb056AlphaDummy013))
                (synCun (synCphi (Class.cv (nb056AlphaDummy014)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0037 (f : Var) :
    (nb056AlphaDummy009 f) ∈
      (((Class.cab (nb056AlphaDummy015 f)
            (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy009 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy016 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy015 f)
            (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy009 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy016 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0038 :
    (nb056AlphaDummy014) ∈
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy014))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0039 (f : Var) :
    (nb056AlphaDummy016 f) ∈
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy016 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0040 :
    (nb056AlphaDummy014) ∈
      (((synCphi (Class.cv (nb056AlphaDummy014)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy014)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0041 (f : Var) :
    (nb056AlphaDummy016 f) ∈
      (((synCphi (Class.cv (nb056AlphaDummy016 f)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy016 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0042 :
    (nb056AlphaDummy005) ∈
      (((Class.cv (nb056AlphaDummy005))).fv ∪ ((Class.cv (nb056AlphaDummy007))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0043 :
    (nb056AlphaDummy005) ∈
      (((synCcompl (Class.cab (nb056AlphaDummy049)
              (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy005))
                (Wff.classEq (Class.cv (nb056AlphaDummy049))
                  (synCphi (Class.cv (nb056AlphaDummy050)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy049)
              (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy007))
                (Wff.classEq (Class.cv (nb056AlphaDummy049))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy050)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0044 (f : Var) :
    (nb056AlphaDummy008 f) ∈
      (((Class.cv (nb056AlphaDummy008 f))).fv ∪ ((Class.cv (nb056AlphaDummy010 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0045 (f : Var) :
    (nb056AlphaDummy008 f) ∈
      (((synCcompl (Class.cab (nb056AlphaDummy051 f)
              (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy008 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                  (synCphi (Class.cv (nb056AlphaDummy052 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy051 f)
              (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy010 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy052 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0044 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0044 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0046 :
    (nb056AlphaDummy005) ∈
      (((Class.cab (nb056AlphaDummy049)
            (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy005))
              (Wff.classEq (Class.cv (nb056AlphaDummy049))
                (synCphi (Class.cv (nb056AlphaDummy050))))))).fv ∪
        ((Class.cab (nb056AlphaDummy049)
            (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy005))
              (Wff.classEq (Class.cv (nb056AlphaDummy049))
                (synCphi (Class.cv (nb056AlphaDummy050))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0047 (f : Var) :
    (nb056AlphaDummy008 f) ∈
      (((Class.cab (nb056AlphaDummy051 f)
            (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy008 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                (synCphi (Class.cv (nb056AlphaDummy052 f))))))).fv ∪
        ((Class.cab (nb056AlphaDummy051 f)
            (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy008 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                (synCphi (Class.cv (nb056AlphaDummy052 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0044 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0044 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0048 :
    (nb056AlphaDummy050) ∈ (((Class.cv (nb056AlphaDummy050))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0049 (f : Var) :
    (nb056AlphaDummy052 f) ∈ (((Class.cv (nb056AlphaDummy052 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0050 :
    (nb056AlphaDummy057) ∈
      (((Wff.classMem (Class.cv (nb056AlphaDummy057)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy057)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy057))).fv) :=
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

theorem nb056_support_mem_0051 (f : Var) :
    (nb056AlphaDummy059 f) ∈
      (((Wff.classMem (Class.cv (nb056AlphaDummy059 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy059 f)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy059 f))).fv) :=
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

theorem nb056_support_mem_0052 :
    (nb056AlphaDummy057) ∈
      (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0053 (f : Var) :
    (nb056AlphaDummy059 f) ∈
      (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0054 :
    (nb056AlphaDummy064) ∈
      (((synCnin (Class.cv (nb056AlphaDummy064)) (Class.cv (nb056AlphaDummy065)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy064))
            (Class.cv (nb056AlphaDummy065)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0055 (f : Var) :
    (nb056AlphaDummy067 f) ∈
      (((synCnin (Class.cv (nb056AlphaDummy067 f))
            (Class.cv (nb056AlphaDummy068 f)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy067 f))
            (Class.cv (nb056AlphaDummy068 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0056 :
    (nb056AlphaDummy064) ∈
      (((Class.cv (nb056AlphaDummy064))).fv ∪ ((Class.cv (nb056AlphaDummy065))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0057 (f : Var) :
    (nb056AlphaDummy067 f) ∈
      (((Class.cv (nb056AlphaDummy067 f))).fv ∪ ((Class.cv (nb056AlphaDummy068 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0058 :
    (nb056AlphaDummy065) ∈
      (((synCnin (Class.cv (nb056AlphaDummy064)) (Class.cv (nb056AlphaDummy065)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy064))
            (Class.cv (nb056AlphaDummy065)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0059 (f : Var) :
    (nb056AlphaDummy068 f) ∈
      (((synCnin (Class.cv (nb056AlphaDummy067 f))
            (Class.cv (nb056AlphaDummy068 f)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy067 f))
            (Class.cv (nb056AlphaDummy068 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0060 :
    (nb056AlphaDummy065) ∈
      (((Class.cv (nb056AlphaDummy064))).fv ∪ ((Class.cv (nb056AlphaDummy065))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0061 (f : Var) :
    (nb056AlphaDummy068 f) ∈
      (((Class.cv (nb056AlphaDummy067 f))).fv ∪ ((Class.cv (nb056AlphaDummy068 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0062 :
    (nb056AlphaDummy064) ∈
      (((synCcompl (Class.cv (nb056AlphaDummy064)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy065)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0063 (f : Var) :
    (nb056AlphaDummy067 f) ∈
      (((synCcompl (Class.cv (nb056AlphaDummy067 f)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy068 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0064 :
    (nb056AlphaDummy064) ∈
      (((Class.cv (nb056AlphaDummy064))).fv ∪ ((Class.cv (nb056AlphaDummy064))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0065 (f : Var) :
    (nb056AlphaDummy067 f) ∈
      (((Class.cv (nb056AlphaDummy067 f))).fv ∪ ((Class.cv (nb056AlphaDummy067 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0066 :
    (nb056AlphaDummy065) ∈
      (((synCcompl (Class.cv (nb056AlphaDummy064)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy065)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0067 (f : Var) :
    (nb056AlphaDummy068 f) ∈
      (((synCcompl (Class.cv (nb056AlphaDummy067 f)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy068 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0068 :
    (nb056AlphaDummy065) ∈
      (((Class.cv (nb056AlphaDummy065))).fv ∪ ((Class.cv (nb056AlphaDummy065))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0069 (f : Var) :
    (nb056AlphaDummy068 f) ∈
      (((Class.cv (nb056AlphaDummy068 f))).fv ∪ ((Class.cv (nb056AlphaDummy068 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0070 :
    (nb056AlphaDummy007) ∈
      (((Class.cv (nb056AlphaDummy005))).fv ∪ ((Class.cv (nb056AlphaDummy007))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0071 :
    (nb056AlphaDummy007) ∈
      (((synCcompl (Class.cab (nb056AlphaDummy049)
              (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy005))
                (Wff.classEq (Class.cv (nb056AlphaDummy049))
                  (synCphi (Class.cv (nb056AlphaDummy050)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy049)
              (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy007))
                (Wff.classEq (Class.cv (nb056AlphaDummy049))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy050)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0072 (f : Var) :
    (nb056AlphaDummy010 f) ∈
      (((Class.cv (nb056AlphaDummy008 f))).fv ∪ ((Class.cv (nb056AlphaDummy010 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0073 (f : Var) :
    (nb056AlphaDummy010 f) ∈
      (((synCcompl (Class.cab (nb056AlphaDummy051 f)
              (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy008 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                  (synCphi (Class.cv (nb056AlphaDummy052 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy051 f)
              (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy010 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy052 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0074 :
    (nb056AlphaDummy007) ∈
      (((Class.cab (nb056AlphaDummy049)
            (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy007))
              (Wff.classEq (Class.cv (nb056AlphaDummy049))
                (synCun (synCphi (Class.cv (nb056AlphaDummy050)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy049)
            (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy007))
              (Wff.classEq (Class.cv (nb056AlphaDummy049))
                (synCun (synCphi (Class.cv (nb056AlphaDummy050)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0075 (f : Var) :
    (nb056AlphaDummy010 f) ∈
      (((Class.cab (nb056AlphaDummy051 f)
            (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy010 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy052 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy051 f)
            (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy010 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy052 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0076 :
    (nb056AlphaDummy050) ∈
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy050))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0077 (f : Var) :
    (nb056AlphaDummy052 f) ∈
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy052 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0078 :
    (nb056AlphaDummy050) ∈
      (((synCphi (Class.cv (nb056AlphaDummy050)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy050)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0079 (f : Var) :
    (nb056AlphaDummy052 f) ∈
      (((synCphi (Class.cv (nb056AlphaDummy052 f)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy052 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0080 :
    (nb056AlphaDummy085) ∈
      (({(nb056AlphaDummy085)} : Finset Var) ∪ ({(nb056AlphaDummy086)} : Finset Var) ∪
        ((synWbr (Class.cv (nb056AlphaDummy086)) (Class.cv (nb056AlphaDummy000))
            (Class.cv (nb056AlphaDummy085)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0081 (f : Var) :
    (nb056AlphaDummy087 f) ∈
      (({(nb056AlphaDummy087 f)} : Finset Var) ∪ ({(nb056AlphaDummy088 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb056AlphaDummy088 f)) (Class.cv f)
            (Class.cv (nb056AlphaDummy087 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0082 :
    (nb056AlphaDummy086) ∈
      (({(nb056AlphaDummy085)} : Finset Var) ∪ ({(nb056AlphaDummy086)} : Finset Var) ∪
        ((synWbr (Class.cv (nb056AlphaDummy086)) (Class.cv (nb056AlphaDummy000))
            (Class.cv (nb056AlphaDummy085)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0083 (f : Var) :
    (nb056AlphaDummy088 f) ∈
      (({(nb056AlphaDummy087 f)} : Finset Var) ∪ ({(nb056AlphaDummy088 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb056AlphaDummy088 f)) (Class.cv f)
            (Class.cv (nb056AlphaDummy087 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0084 :
    (nb056AlphaDummy085) ∈
      (((Class.cv (nb056AlphaDummy085))).fv ∪ ((Class.cv (nb056AlphaDummy086))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0085 :
    (nb056AlphaDummy085) ∈
      (((synCcompl (Class.cab (nb056AlphaDummy091)
              (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy085))
                (Wff.classEq (Class.cv (nb056AlphaDummy091))
                  (synCphi (Class.cv (nb056AlphaDummy092)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy091)
              (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy086))
                (Wff.classEq (Class.cv (nb056AlphaDummy091))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy092)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0084) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0084) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0086 (f : Var) :
    (nb056AlphaDummy087 f) ∈
      (((Class.cv (nb056AlphaDummy087 f))).fv ∪ ((Class.cv (nb056AlphaDummy088 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0087 (f : Var) :
    (nb056AlphaDummy087 f) ∈
      (((synCcompl (Class.cab (nb056AlphaDummy093 f)
              (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy087 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                  (synCphi (Class.cv (nb056AlphaDummy094 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy093 f)
              (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy088 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy094 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0086 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0086 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0088 :
    (nb056AlphaDummy085) ∈
      (((Class.cab (nb056AlphaDummy091)
            (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy085))
              (Wff.classEq (Class.cv (nb056AlphaDummy091))
                (synCphi (Class.cv (nb056AlphaDummy092))))))).fv ∪
        ((Class.cab (nb056AlphaDummy091)
            (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy085))
              (Wff.classEq (Class.cv (nb056AlphaDummy091))
                (synCphi (Class.cv (nb056AlphaDummy092))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0084) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0084) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0089 (f : Var) :
    (nb056AlphaDummy087 f) ∈
      (((Class.cab (nb056AlphaDummy093 f)
            (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                (synCphi (Class.cv (nb056AlphaDummy094 f))))))).fv ∪
        ((Class.cab (nb056AlphaDummy093 f)
            (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                (synCphi (Class.cv (nb056AlphaDummy094 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0086 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0086 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0090 :
    (nb056AlphaDummy092) ∈ (((Class.cv (nb056AlphaDummy092))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0091 (f : Var) :
    (nb056AlphaDummy094 f) ∈ (((Class.cv (nb056AlphaDummy094 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0092 :
    (nb056AlphaDummy099) ∈
      (((Wff.classMem (Class.cv (nb056AlphaDummy099)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy099)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy099))).fv) :=
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

theorem nb056_support_mem_0093 (f : Var) :
    (nb056AlphaDummy101 f) ∈
      (((Wff.classMem (Class.cv (nb056AlphaDummy101 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy101 f)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy101 f))).fv) :=
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

theorem nb056_support_mem_0094 :
    (nb056AlphaDummy099) ∈
      (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0095 (f : Var) :
    (nb056AlphaDummy101 f) ∈
      (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0096 :
    (nb056AlphaDummy106) ∈
      (((synCnin (Class.cv (nb056AlphaDummy106)) (Class.cv (nb056AlphaDummy107)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy106))
            (Class.cv (nb056AlphaDummy107)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0097 (f : Var) :
    (nb056AlphaDummy109 f) ∈
      (((synCnin (Class.cv (nb056AlphaDummy109 f))
            (Class.cv (nb056AlphaDummy110 f)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy109 f))
            (Class.cv (nb056AlphaDummy110 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0098 :
    (nb056AlphaDummy106) ∈
      (((Class.cv (nb056AlphaDummy106))).fv ∪ ((Class.cv (nb056AlphaDummy107))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0099 (f : Var) :
    (nb056AlphaDummy109 f) ∈
      (((Class.cv (nb056AlphaDummy109 f))).fv ∪ ((Class.cv (nb056AlphaDummy110 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0100 :
    (nb056AlphaDummy107) ∈
      (((synCnin (Class.cv (nb056AlphaDummy106)) (Class.cv (nb056AlphaDummy107)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy106))
            (Class.cv (nb056AlphaDummy107)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0101 (f : Var) :
    (nb056AlphaDummy110 f) ∈
      (((synCnin (Class.cv (nb056AlphaDummy109 f))
            (Class.cv (nb056AlphaDummy110 f)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy109 f))
            (Class.cv (nb056AlphaDummy110 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0102 :
    (nb056AlphaDummy107) ∈
      (((Class.cv (nb056AlphaDummy106))).fv ∪ ((Class.cv (nb056AlphaDummy107))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0103 (f : Var) :
    (nb056AlphaDummy110 f) ∈
      (((Class.cv (nb056AlphaDummy109 f))).fv ∪ ((Class.cv (nb056AlphaDummy110 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0104 :
    (nb056AlphaDummy106) ∈
      (((synCcompl (Class.cv (nb056AlphaDummy106)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy107)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0105 (f : Var) :
    (nb056AlphaDummy109 f) ∈
      (((synCcompl (Class.cv (nb056AlphaDummy109 f)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy110 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0106 :
    (nb056AlphaDummy106) ∈
      (((Class.cv (nb056AlphaDummy106))).fv ∪ ((Class.cv (nb056AlphaDummy106))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0107 (f : Var) :
    (nb056AlphaDummy109 f) ∈
      (((Class.cv (nb056AlphaDummy109 f))).fv ∪ ((Class.cv (nb056AlphaDummy109 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0108 :
    (nb056AlphaDummy107) ∈
      (((synCcompl (Class.cv (nb056AlphaDummy106)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy107)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0109 (f : Var) :
    (nb056AlphaDummy110 f) ∈
      (((synCcompl (Class.cv (nb056AlphaDummy109 f)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy110 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0110 :
    (nb056AlphaDummy107) ∈
      (((Class.cv (nb056AlphaDummy107))).fv ∪ ((Class.cv (nb056AlphaDummy107))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0111 (f : Var) :
    (nb056AlphaDummy110 f) ∈
      (((Class.cv (nb056AlphaDummy110 f))).fv ∪ ((Class.cv (nb056AlphaDummy110 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0112 :
    (nb056AlphaDummy086) ∈
      (((Class.cv (nb056AlphaDummy085))).fv ∪ ((Class.cv (nb056AlphaDummy086))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0113 :
    (nb056AlphaDummy086) ∈
      (((synCcompl (Class.cab (nb056AlphaDummy091)
              (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy085))
                (Wff.classEq (Class.cv (nb056AlphaDummy091))
                  (synCphi (Class.cv (nb056AlphaDummy092)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy091)
              (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy086))
                (Wff.classEq (Class.cv (nb056AlphaDummy091))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy092)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0114 (f : Var) :
    (nb056AlphaDummy088 f) ∈
      (((Class.cv (nb056AlphaDummy087 f))).fv ∪ ((Class.cv (nb056AlphaDummy088 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0115 (f : Var) :
    (nb056AlphaDummy088 f) ∈
      (((synCcompl (Class.cab (nb056AlphaDummy093 f)
              (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy087 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                  (synCphi (Class.cv (nb056AlphaDummy094 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy093 f)
              (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy088 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy094 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0116 :
    (nb056AlphaDummy086) ∈
      (((Class.cab (nb056AlphaDummy091)
            (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy086))
              (Wff.classEq (Class.cv (nb056AlphaDummy091))
                (synCun (synCphi (Class.cv (nb056AlphaDummy092)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy091)
            (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy086))
              (Wff.classEq (Class.cv (nb056AlphaDummy091))
                (synCun (synCphi (Class.cv (nb056AlphaDummy092)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0117 (f : Var) :
    (nb056AlphaDummy088 f) ∈
      (((Class.cab (nb056AlphaDummy093 f)
            (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy094 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy093 f)
            (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy094 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0118 :
    (nb056AlphaDummy092) ∈
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy092))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0119 (f : Var) :
    (nb056AlphaDummy094 f) ∈
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy094 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0120 :
    (nb056AlphaDummy092) ∈
      (((synCphi (Class.cv (nb056AlphaDummy092)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy092)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0121 (f : Var) :
    (nb056AlphaDummy094 f) ∈
      (((synCphi (Class.cv (nb056AlphaDummy094 f)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy094 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0122 :
    (nb056AlphaDummy086) ∈
      (((Class.cv (nb056AlphaDummy086))).fv ∪ ((Class.cv (nb056AlphaDummy085))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0123 :
    (nb056AlphaDummy086) ∈
      (((synCcompl (Class.cab (nb056AlphaDummy127)
              (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy086))
                (Wff.classEq (Class.cv (nb056AlphaDummy127))
                  (synCphi (Class.cv (nb056AlphaDummy128)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy127)
              (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy085))
                (Wff.classEq (Class.cv (nb056AlphaDummy127))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy128)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0122) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0122) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0124 (f : Var) :
    (nb056AlphaDummy088 f) ∈
      (((Class.cv (nb056AlphaDummy088 f))).fv ∪ ((Class.cv (nb056AlphaDummy087 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0125 (f : Var) :
    (nb056AlphaDummy088 f) ∈
      (((synCcompl (Class.cab (nb056AlphaDummy129 f)
              (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy088 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                  (synCphi (Class.cv (nb056AlphaDummy130 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy129 f)
              (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy087 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy130 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0124 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0124 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0126 :
    (nb056AlphaDummy086) ∈
      (((Class.cab (nb056AlphaDummy127)
            (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy086))
              (Wff.classEq (Class.cv (nb056AlphaDummy127))
                (synCphi (Class.cv (nb056AlphaDummy128))))))).fv ∪
        ((Class.cab (nb056AlphaDummy127)
            (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy086))
              (Wff.classEq (Class.cv (nb056AlphaDummy127))
                (synCphi (Class.cv (nb056AlphaDummy128))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0122) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0122) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0127 (f : Var) :
    (nb056AlphaDummy088 f) ∈
      (((Class.cab (nb056AlphaDummy129 f)
            (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                (synCphi (Class.cv (nb056AlphaDummy130 f))))))).fv ∪
        ((Class.cab (nb056AlphaDummy129 f)
            (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                (synCphi (Class.cv (nb056AlphaDummy130 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0124 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0124 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
