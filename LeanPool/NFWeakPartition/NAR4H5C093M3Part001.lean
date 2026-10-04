/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4H5C093M3Part001. -/


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

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_000`. -/
@[expose]
noncomputable def nb093AlphaDummy000 (A : Class) : Var :=
  (freshVar ((A).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_001`. -/
@[expose]
noncomputable def nb093AlphaDummy001 (A : Class) : Var :=
  (freshVar ((A).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_002`. -/
@[expose]
noncomputable def nb093AlphaDummy002 (A : Class) : Var :=
  (freshVar (((synCnin (synClntpc A)
          (synCopab (nb093AlphaDummy001 A) (nb093AlphaDummy000 A) (synWbr
              (synCdif (Class.cv (nb093AlphaDummy001 A))
                (synCcnv (Class.cv (nb093AlphaDummy001 A))))
              (synCfound) (Class.cv (nb093AlphaDummy000 A)))))).fv ∪
      ((synCnin (synClntpc A) (synCopab (nb093AlphaDummy001 A) (nb093AlphaDummy000 A)
            (synWbr (synCdif (Class.cv (nb093AlphaDummy001 A))
                (synCcnv (Class.cv (nb093AlphaDummy001 A))))
              (synCfound) (Class.cv (nb093AlphaDummy000 A)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_003`. -/
@[expose]
noncomputable def nb093AlphaDummy003 (A : Class) (r : Var) (d : Var) : Var :=
  (freshVar (((synCnin (synClntpc A) (synCopab r d
            (synWbr (synCdif (Class.cv r) (synCcnv (Class.cv r))) (synCfound)
              (Class.cv d))))).fv ∪ ((synCnin (synClntpc A) (synCopab r d
            (synWbr (synCdif (Class.cv r) (synCcnv (Class.cv r))) (synCfound)
              (Class.cv d))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_004`. -/
@[expose]
noncomputable def nb093AlphaDummy004 (A : Class) : Var :=
  (freshVar (((synClntpc A)).fv ∪
      ((synCopab (nb093AlphaDummy001 A) (nb093AlphaDummy000 A) (synWbr
            (synCdif (Class.cv (nb093AlphaDummy001 A))
              (synCcnv (Class.cv (nb093AlphaDummy001 A))))
            (synCfound) (Class.cv (nb093AlphaDummy000 A))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_005`. -/
@[expose]
noncomputable def nb093AlphaDummy005 (A : Class) (r : Var) (d : Var) : Var :=
  (freshVar (((synClntpc A)).fv ∪ ((synCopab r d
          (synWbr (synCdif (Class.cv r) (synCcnv (Class.cv r))) (synCfound)
            (Class.cv d)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_006`. -/
@[expose]
noncomputable def nb093AlphaDummy006 (A : Class) : Var :=
  (freshVar (({(nb093AlphaDummy001 A)} : Finset Var) ∪
        ({(nb093AlphaDummy000 A)} : Finset Var) ∪ ((synWbr
          (synCdif (Class.cv (nb093AlphaDummy001 A))
            (synCcnv (Class.cv (nb093AlphaDummy001 A))))
          (synCfound) (Class.cv (nb093AlphaDummy000 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_007`. -/
@[expose]
noncomputable def nb093AlphaDummy007 (r : Var) (d : Var) : Var :=
  (freshVar (({ r } : Finset Var) ∪ ({ d } : Finset Var) ∪
      ((synWbr (synCdif (Class.cv r) (synCcnv (Class.cv r))) (synCfound) (Class.cv d))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_008`. -/
@[expose]
noncomputable def nb093AlphaDummy008 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy001 A))).fv ∪
      ((Class.cv (nb093AlphaDummy000 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_009`. -/
@[expose]
noncomputable def nb093AlphaDummy009 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy001 A))).fv ∪
      ((Class.cv (nb093AlphaDummy000 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_010`. -/
@[expose]
noncomputable def nb093AlphaDummy010 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv d)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_011`. -/
@[expose]
noncomputable def nb093AlphaDummy011 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv d)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_012`. -/
@[expose]
noncomputable def nb093AlphaDummy012 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb093AlphaDummy008 A)
            (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                (synCphi (Class.cv (nb093AlphaDummy009 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb093AlphaDummy008 A)
            (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy009 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_013`. -/
@[expose]
noncomputable def nb093AlphaDummy013 (r : Var) (d : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb093AlphaDummy010 r d)
            (synWrex (nb093AlphaDummy011 r d) (Class.cv r)
              (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                (synCphi (Class.cv (nb093AlphaDummy011 r d)))))))).fv ∪ ((synCcompl
          (Class.cab (nb093AlphaDummy010 r d)
            (synWrex (nb093AlphaDummy011 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                (synCun (synCphi (Class.cv (nb093AlphaDummy011 r d)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_014`. -/
@[expose]
noncomputable def nb093AlphaDummy014 (A : Class) : Var :=
  (freshVar (((Class.cab (nb093AlphaDummy008 A)
          (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy001 A))
            (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
              (synCphi (Class.cv (nb093AlphaDummy009 A))))))).fv ∪
      ((Class.cab (nb093AlphaDummy008 A)
          (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy001 A))
            (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
              (synCphi (Class.cv (nb093AlphaDummy009 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_015`. -/
@[expose]
noncomputable def nb093AlphaDummy015 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cab (nb093AlphaDummy010 r d)
          (synWrex (nb093AlphaDummy011 r d) (Class.cv r)
            (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
              (synCphi (Class.cv (nb093AlphaDummy011 r d))))))).fv ∪
      ((Class.cab (nb093AlphaDummy010 r d) (synWrex (nb093AlphaDummy011 r d) (Class.cv r)
            (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
              (synCphi (Class.cv (nb093AlphaDummy011 r d))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_016`. -/
@[expose]
noncomputable def nb093AlphaDummy016 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy009 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_017`. -/
@[expose]
noncomputable def nb093AlphaDummy017 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy009 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_018`. -/
@[expose]
noncomputable def nb093AlphaDummy018 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy011 r d))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_019`. -/
@[expose]
noncomputable def nb093AlphaDummy019 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy011 r d))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_020`. -/
@[expose]
noncomputable def nb093AlphaDummy020 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb093AlphaDummy016 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb093AlphaDummy016 A)) (synC1c))).fv ∪
      ((Class.cv (nb093AlphaDummy016 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_021`. -/
@[expose]
noncomputable def nb093AlphaDummy021 (r : Var) (d : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb093AlphaDummy018 r d)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb093AlphaDummy018 r d)) (synC1c))).fv ∪
      ((Class.cv (nb093AlphaDummy018 r d))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_022`. -/
@[expose]
noncomputable def nb093AlphaDummy022 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy016 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_023`. -/
@[expose]
noncomputable def nb093AlphaDummy023 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy016 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_024`. -/
@[expose]
noncomputable def nb093AlphaDummy024 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy016 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_025`. -/
@[expose]
noncomputable def nb093AlphaDummy025 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy018 r d))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_026`. -/
@[expose]
noncomputable def nb093AlphaDummy026 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy018 r d))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_027`. -/
@[expose]
noncomputable def nb093AlphaDummy027 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy018 r d))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_028`. -/
@[expose]
noncomputable def nb093AlphaDummy028 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb093AlphaDummy023 A))
          (Class.cv (nb093AlphaDummy024 A)))).fv ∪
      ((synCnin (Class.cv (nb093AlphaDummy023 A)) (Class.cv (nb093AlphaDummy024 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_029`. -/
@[expose]
noncomputable def nb093AlphaDummy029 (r : Var) (d : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb093AlphaDummy026 r d))
          (Class.cv (nb093AlphaDummy027 r d)))).fv ∪
      ((synCnin (Class.cv (nb093AlphaDummy026 r d))
          (Class.cv (nb093AlphaDummy027 r d)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_030`. -/
@[expose]
noncomputable def nb093AlphaDummy030 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy023 A))).fv ∪
      ((Class.cv (nb093AlphaDummy024 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_031`. -/
@[expose]
noncomputable def nb093AlphaDummy031 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy026 r d))).fv ∪
      ((Class.cv (nb093AlphaDummy027 r d))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_032`. -/
@[expose]
noncomputable def nb093AlphaDummy032 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb093AlphaDummy023 A)))).fv ∪
      ((synCcompl (Class.cv (nb093AlphaDummy024 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_033`. -/
@[expose]
noncomputable def nb093AlphaDummy033 (r : Var) (d : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb093AlphaDummy026 r d)))).fv ∪
      ((synCcompl (Class.cv (nb093AlphaDummy027 r d)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_034`. -/
@[expose]
noncomputable def nb093AlphaDummy034 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy023 A))).fv ∪
      ((Class.cv (nb093AlphaDummy023 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_035`. -/
@[expose]
noncomputable def nb093AlphaDummy035 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy026 r d))).fv ∪
      ((Class.cv (nb093AlphaDummy026 r d))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_036`. -/
@[expose]
noncomputable def nb093AlphaDummy036 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy024 A))).fv ∪
      ((Class.cv (nb093AlphaDummy024 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_037`. -/
@[expose]
noncomputable def nb093AlphaDummy037 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy027 r d))).fv ∪
      ((Class.cv (nb093AlphaDummy027 r d))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_038`. -/
@[expose]
noncomputable def nb093AlphaDummy038 (A : Class) : Var :=
  (freshVar (((Class.cab (nb093AlphaDummy008 A)
          (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy000 A))
            (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
              (synCun (synCphi (Class.cv (nb093AlphaDummy009 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy008 A)
          (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy000 A))
            (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
              (synCun (synCphi (Class.cv (nb093AlphaDummy009 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_039`. -/
@[expose]
noncomputable def nb093AlphaDummy039 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cab (nb093AlphaDummy010 r d)
          (synWrex (nb093AlphaDummy011 r d) (Class.cv d)
            (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
              (synCun (synCphi (Class.cv (nb093AlphaDummy011 r d)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy010 r d)
          (synWrex (nb093AlphaDummy011 r d) (Class.cv d)
            (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
              (synCun (synCphi (Class.cv (nb093AlphaDummy011 r d)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_040`. -/
@[expose]
noncomputable def nb093AlphaDummy040 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb093AlphaDummy009 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_041`. -/
@[expose]
noncomputable def nb093AlphaDummy041 (r : Var) (d : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb093AlphaDummy011 r d))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_042`. -/
@[expose]
noncomputable def nb093AlphaDummy042 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb093AlphaDummy009 A)))).fv ∪
      ((synCphi (Class.cv (nb093AlphaDummy009 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_043`. -/
@[expose]
noncomputable def nb093AlphaDummy043 (r : Var) (d : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb093AlphaDummy011 r d)))).fv ∪
      ((synCphi (Class.cv (nb093AlphaDummy011 r d)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_044`. -/
@[expose]
noncomputable def nb093AlphaDummy044 (A : Class) : Var :=
  (freshVar (((synCdif (Class.cv (nb093AlphaDummy001 A))
          (synCcnv (Class.cv (nb093AlphaDummy001 A))))).fv ∪
      ((Class.cv (nb093AlphaDummy000 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_045`. -/
@[expose]
noncomputable def nb093AlphaDummy045 (A : Class) : Var :=
  (freshVar (((synCdif (Class.cv (nb093AlphaDummy001 A))
          (synCcnv (Class.cv (nb093AlphaDummy001 A))))).fv ∪
      ((Class.cv (nb093AlphaDummy000 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_046`. -/
@[expose]
noncomputable def nb093AlphaDummy046 (r : Var) (d : Var) : Var :=
  (freshVar (((synCdif (Class.cv r) (synCcnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_047`. -/
@[expose]
noncomputable def nb093AlphaDummy047 (r : Var) (d : Var) : Var :=
  (freshVar (((synCdif (Class.cv r) (synCcnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_048`. -/
@[expose]
noncomputable def nb093AlphaDummy048 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb093AlphaDummy044 A)
            (synWrex (nb093AlphaDummy045 A) (synCdif (Class.cv (nb093AlphaDummy001 A))
                (synCcnv (Class.cv (nb093AlphaDummy001 A))))
              (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                (synCphi (Class.cv (nb093AlphaDummy045 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb093AlphaDummy044 A)
            (synWrex (nb093AlphaDummy045 A) (Class.cv (nb093AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy045 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_049`. -/
@[expose]
noncomputable def nb093AlphaDummy049 (r : Var) (d : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb093AlphaDummy046 r d)
            (synWrex (nb093AlphaDummy047 r d)
              (synCdif (Class.cv r) (synCcnv (Class.cv r)))
              (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                (synCphi (Class.cv (nb093AlphaDummy047 r d)))))))).fv ∪ ((synCcompl
          (Class.cab (nb093AlphaDummy046 r d)
            (synWrex (nb093AlphaDummy047 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                (synCun (synCphi (Class.cv (nb093AlphaDummy047 r d)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_050`. -/
@[expose]
noncomputable def nb093AlphaDummy050 (A : Class) : Var :=
  (freshVar (((Class.cab (nb093AlphaDummy044 A) (synWrex (nb093AlphaDummy045 A)
            (synCdif (Class.cv (nb093AlphaDummy001 A))
              (synCcnv (Class.cv (nb093AlphaDummy001 A))))
            (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
              (synCphi (Class.cv (nb093AlphaDummy045 A))))))).fv ∪
      ((Class.cab (nb093AlphaDummy044 A) (synWrex (nb093AlphaDummy045 A)
            (synCdif (Class.cv (nb093AlphaDummy001 A))
              (synCcnv (Class.cv (nb093AlphaDummy001 A))))
            (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
              (synCphi (Class.cv (nb093AlphaDummy045 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_051`. -/
@[expose]
noncomputable def nb093AlphaDummy051 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cab (nb093AlphaDummy046 r d) (synWrex (nb093AlphaDummy047 r d)
            (synCdif (Class.cv r) (synCcnv (Class.cv r)))
            (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
              (synCphi (Class.cv (nb093AlphaDummy047 r d))))))).fv ∪
      ((Class.cab (nb093AlphaDummy046 r d) (synWrex (nb093AlphaDummy047 r d)
            (synCdif (Class.cv r) (synCcnv (Class.cv r)))
            (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
              (synCphi (Class.cv (nb093AlphaDummy047 r d))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_052`. -/
@[expose]
noncomputable def nb093AlphaDummy052 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb093AlphaDummy001 A))
          (synCcompl (synCcnv (Class.cv (nb093AlphaDummy001 A)))))).fv ∪
      ((synCnin (Class.cv (nb093AlphaDummy001 A))
          (synCcompl (synCcnv (Class.cv (nb093AlphaDummy001 A)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_053`. -/
@[expose]
noncomputable def nb093AlphaDummy053 (r : Var) : Var :=
  (freshVar (((synCnin (Class.cv r) (synCcompl (synCcnv (Class.cv r))))).fv ∪
      ((synCnin (Class.cv r) (synCcompl (synCcnv (Class.cv r))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_054`. -/
@[expose]
noncomputable def nb093AlphaDummy054 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy001 A))).fv ∪
      ((synCcompl (synCcnv (Class.cv (nb093AlphaDummy001 A))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_055`. -/
@[expose]
noncomputable def nb093AlphaDummy055 (r : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((synCcompl (synCcnv (Class.cv r)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_056`. -/
@[expose]
noncomputable def nb093AlphaDummy056 (A : Class) : Var :=
  (freshVar (((synCcnv (Class.cv (nb093AlphaDummy001 A)))).fv ∪
      ((synCcnv (Class.cv (nb093AlphaDummy001 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_057`. -/
@[expose]
noncomputable def nb093AlphaDummy057 (r : Var) : Var :=
  (freshVar (((synCcnv (Class.cv r))).fv ∪ ((synCcnv (Class.cv r))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_058`. -/
@[expose]
noncomputable def nb093AlphaDummy058 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy001 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_059`. -/
@[expose]
noncomputable def nb093AlphaDummy059 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy001 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_060`. -/
@[expose]
noncomputable def nb093AlphaDummy060 (r : Var) : Var :=
  (freshVar (((Class.cv r)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_061`. -/
@[expose]
noncomputable def nb093AlphaDummy061 (r : Var) : Var :=
  (freshVar (((Class.cv r)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_062`. -/
@[expose]
noncomputable def nb093AlphaDummy062 (A : Class) : Var :=
  (freshVar (({(nb093AlphaDummy058 A)} : Finset Var) ∪
        ({(nb093AlphaDummy059 A)} : Finset Var) ∪
      ((synWbr (Class.cv (nb093AlphaDummy059 A)) (Class.cv (nb093AlphaDummy001 A))
          (Class.cv (nb093AlphaDummy058 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_063`. -/
@[expose]
noncomputable def nb093AlphaDummy063 (r : Var) : Var :=
  (freshVar (({(nb093AlphaDummy060 r)} : Finset Var) ∪
        ({(nb093AlphaDummy061 r)} : Finset Var) ∪
      ((synWbr (Class.cv (nb093AlphaDummy061 r)) (Class.cv r)
          (Class.cv (nb093AlphaDummy060 r)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_064`. -/
@[expose]
noncomputable def nb093AlphaDummy064 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy058 A))).fv ∪
      ((Class.cv (nb093AlphaDummy059 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_065`. -/
@[expose]
noncomputable def nb093AlphaDummy065 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy058 A))).fv ∪
      ((Class.cv (nb093AlphaDummy059 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_066`. -/
@[expose]
noncomputable def nb093AlphaDummy066 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy060 r))).fv ∪
      ((Class.cv (nb093AlphaDummy061 r))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_067`. -/
@[expose]
noncomputable def nb093AlphaDummy067 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy060 r))).fv ∪
      ((Class.cv (nb093AlphaDummy061 r))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_068`. -/
@[expose]
noncomputable def nb093AlphaDummy068 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb093AlphaDummy064 A)
            (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy058 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                (synCphi (Class.cv (nb093AlphaDummy065 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb093AlphaDummy064 A)
            (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy059 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy065 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_069`. -/
@[expose]
noncomputable def nb093AlphaDummy069 (r : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb093AlphaDummy066 r)
            (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy060 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                (synCphi (Class.cv (nb093AlphaDummy067 r)))))))).fv ∪ ((synCcompl
          (Class.cab (nb093AlphaDummy066 r)
            (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy061 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                (synCun (synCphi (Class.cv (nb093AlphaDummy067 r)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_070`. -/
@[expose]
noncomputable def nb093AlphaDummy070 (A : Class) : Var :=
  (freshVar (((Class.cab (nb093AlphaDummy064 A)
          (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy058 A))
            (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
              (synCphi (Class.cv (nb093AlphaDummy065 A))))))).fv ∪
      ((Class.cab (nb093AlphaDummy064 A)
          (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy058 A))
            (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
              (synCphi (Class.cv (nb093AlphaDummy065 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_071`. -/
@[expose]
noncomputable def nb093AlphaDummy071 (r : Var) : Var :=
  (freshVar (((Class.cab (nb093AlphaDummy066 r)
          (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy060 r))
            (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
              (synCphi (Class.cv (nb093AlphaDummy067 r))))))).fv ∪
      ((Class.cab (nb093AlphaDummy066 r)
          (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy060 r))
            (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
              (synCphi (Class.cv (nb093AlphaDummy067 r))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_072`. -/
@[expose]
noncomputable def nb093AlphaDummy072 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy065 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_073`. -/
@[expose]
noncomputable def nb093AlphaDummy073 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy065 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_074`. -/
@[expose]
noncomputable def nb093AlphaDummy074 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy067 r))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_075`. -/
@[expose]
noncomputable def nb093AlphaDummy075 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy067 r))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_076`. -/
@[expose]
noncomputable def nb093AlphaDummy076 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb093AlphaDummy072 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb093AlphaDummy072 A)) (synC1c))).fv ∪
      ((Class.cv (nb093AlphaDummy072 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_077`. -/
@[expose]
noncomputable def nb093AlphaDummy077 (r : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb093AlphaDummy074 r)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb093AlphaDummy074 r)) (synC1c))).fv ∪
      ((Class.cv (nb093AlphaDummy074 r))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_078`. -/
@[expose]
noncomputable def nb093AlphaDummy078 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy072 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_079`. -/
@[expose]
noncomputable def nb093AlphaDummy079 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy072 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_080`. -/
@[expose]
noncomputable def nb093AlphaDummy080 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy072 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_081`. -/
@[expose]
noncomputable def nb093AlphaDummy081 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_082`. -/
@[expose]
noncomputable def nb093AlphaDummy082 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_083`. -/
@[expose]
noncomputable def nb093AlphaDummy083 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_084`. -/
@[expose]
noncomputable def nb093AlphaDummy084 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb093AlphaDummy079 A))
          (Class.cv (nb093AlphaDummy080 A)))).fv ∪
      ((synCnin (Class.cv (nb093AlphaDummy079 A)) (Class.cv (nb093AlphaDummy080 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_085`. -/
@[expose]
noncomputable def nb093AlphaDummy085 (r : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb093AlphaDummy082 r))
          (Class.cv (nb093AlphaDummy083 r)))).fv ∪
      ((synCnin (Class.cv (nb093AlphaDummy082 r)) (Class.cv (nb093AlphaDummy083 r)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_086`. -/
@[expose]
noncomputable def nb093AlphaDummy086 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy079 A))).fv ∪
      ((Class.cv (nb093AlphaDummy080 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_087`. -/
@[expose]
noncomputable def nb093AlphaDummy087 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy082 r))).fv ∪
      ((Class.cv (nb093AlphaDummy083 r))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_088`. -/
@[expose]
noncomputable def nb093AlphaDummy088 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb093AlphaDummy079 A)))).fv ∪
      ((synCcompl (Class.cv (nb093AlphaDummy080 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_089`. -/
@[expose]
noncomputable def nb093AlphaDummy089 (r : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb093AlphaDummy082 r)))).fv ∪
      ((synCcompl (Class.cv (nb093AlphaDummy083 r)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_090`. -/
@[expose]
noncomputable def nb093AlphaDummy090 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy079 A))).fv ∪
      ((Class.cv (nb093AlphaDummy079 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_091`. -/
@[expose]
noncomputable def nb093AlphaDummy091 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy082 r))).fv ∪
      ((Class.cv (nb093AlphaDummy082 r))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_092`. -/
@[expose]
noncomputable def nb093AlphaDummy092 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy080 A))).fv ∪
      ((Class.cv (nb093AlphaDummy080 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_093`. -/
@[expose]
noncomputable def nb093AlphaDummy093 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy083 r))).fv ∪
      ((Class.cv (nb093AlphaDummy083 r))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_094`. -/
@[expose]
noncomputable def nb093AlphaDummy094 (A : Class) : Var :=
  (freshVar (((Class.cab (nb093AlphaDummy064 A)
          (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy059 A))
            (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
              (synCun (synCphi (Class.cv (nb093AlphaDummy065 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy064 A)
          (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy059 A))
            (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
              (synCun (synCphi (Class.cv (nb093AlphaDummy065 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_095`. -/
@[expose]
noncomputable def nb093AlphaDummy095 (r : Var) : Var :=
  (freshVar (((Class.cab (nb093AlphaDummy066 r)
          (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy061 r))
            (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
              (synCun (synCphi (Class.cv (nb093AlphaDummy067 r)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy066 r)
          (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy061 r))
            (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
              (synCun (synCphi (Class.cv (nb093AlphaDummy067 r)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_096`. -/
@[expose]
noncomputable def nb093AlphaDummy096 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb093AlphaDummy065 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_097`. -/
@[expose]
noncomputable def nb093AlphaDummy097 (r : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb093AlphaDummy067 r))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_098`. -/
@[expose]
noncomputable def nb093AlphaDummy098 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb093AlphaDummy065 A)))).fv ∪
      ((synCphi (Class.cv (nb093AlphaDummy065 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_099`. -/
@[expose]
noncomputable def nb093AlphaDummy099 (r : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb093AlphaDummy067 r)))).fv ∪
      ((synCphi (Class.cv (nb093AlphaDummy067 r)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_100`. -/
@[expose]
noncomputable def nb093AlphaDummy100 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy059 A))).fv ∪
      ((Class.cv (nb093AlphaDummy058 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_101`. -/
@[expose]
noncomputable def nb093AlphaDummy101 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy059 A))).fv ∪
      ((Class.cv (nb093AlphaDummy058 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_102`. -/
@[expose]
noncomputable def nb093AlphaDummy102 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy061 r))).fv ∪
      ((Class.cv (nb093AlphaDummy060 r))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_103`. -/
@[expose]
noncomputable def nb093AlphaDummy103 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy061 r))).fv ∪
      ((Class.cv (nb093AlphaDummy060 r))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_104`. -/
@[expose]
noncomputable def nb093AlphaDummy104 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb093AlphaDummy100 A)
            (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy059 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                (synCphi (Class.cv (nb093AlphaDummy101 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb093AlphaDummy100 A)
            (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy058 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy101 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_105`. -/
@[expose]
noncomputable def nb093AlphaDummy105 (r : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb093AlphaDummy102 r)
            (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy061 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                (synCphi (Class.cv (nb093AlphaDummy103 r)))))))).fv ∪ ((synCcompl
          (Class.cab (nb093AlphaDummy102 r)
            (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy060 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                (synCun (synCphi (Class.cv (nb093AlphaDummy103 r)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_106`. -/
@[expose]
noncomputable def nb093AlphaDummy106 (A : Class) : Var :=
  (freshVar (((Class.cab (nb093AlphaDummy100 A)
          (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy059 A))
            (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
              (synCphi (Class.cv (nb093AlphaDummy101 A))))))).fv ∪
      ((Class.cab (nb093AlphaDummy100 A)
          (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy059 A))
            (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
              (synCphi (Class.cv (nb093AlphaDummy101 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_107`. -/
@[expose]
noncomputable def nb093AlphaDummy107 (r : Var) : Var :=
  (freshVar (((Class.cab (nb093AlphaDummy102 r)
          (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy061 r))
            (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
              (synCphi (Class.cv (nb093AlphaDummy103 r))))))).fv ∪
      ((Class.cab (nb093AlphaDummy102 r)
          (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy061 r))
            (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
              (synCphi (Class.cv (nb093AlphaDummy103 r))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_108`. -/
@[expose]
noncomputable def nb093AlphaDummy108 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy101 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_109`. -/
@[expose]
noncomputable def nb093AlphaDummy109 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy101 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_110`. -/
@[expose]
noncomputable def nb093AlphaDummy110 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy103 r))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_111`. -/
@[expose]
noncomputable def nb093AlphaDummy111 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy103 r))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_112`. -/
@[expose]
noncomputable def nb093AlphaDummy112 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb093AlphaDummy108 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb093AlphaDummy108 A)) (synC1c))).fv ∪
      ((Class.cv (nb093AlphaDummy108 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_113`. -/
@[expose]
noncomputable def nb093AlphaDummy113 (r : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb093AlphaDummy110 r)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb093AlphaDummy110 r)) (synC1c))).fv ∪
      ((Class.cv (nb093AlphaDummy110 r))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_114`. -/
@[expose]
noncomputable def nb093AlphaDummy114 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy108 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_115`. -/
@[expose]
noncomputable def nb093AlphaDummy115 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy108 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_116`. -/
@[expose]
noncomputable def nb093AlphaDummy116 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy108 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_117`. -/
@[expose]
noncomputable def nb093AlphaDummy117 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_118`. -/
@[expose]
noncomputable def nb093AlphaDummy118 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_119`. -/
@[expose]
noncomputable def nb093AlphaDummy119 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_120`. -/
@[expose]
noncomputable def nb093AlphaDummy120 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb093AlphaDummy115 A))
          (Class.cv (nb093AlphaDummy116 A)))).fv ∪
      ((synCnin (Class.cv (nb093AlphaDummy115 A)) (Class.cv (nb093AlphaDummy116 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_121`. -/
@[expose]
noncomputable def nb093AlphaDummy121 (r : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb093AlphaDummy118 r))
          (Class.cv (nb093AlphaDummy119 r)))).fv ∪
      ((synCnin (Class.cv (nb093AlphaDummy118 r)) (Class.cv (nb093AlphaDummy119 r)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_122`. -/
@[expose]
noncomputable def nb093AlphaDummy122 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy115 A))).fv ∪
      ((Class.cv (nb093AlphaDummy116 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_123`. -/
@[expose]
noncomputable def nb093AlphaDummy123 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy118 r))).fv ∪
      ((Class.cv (nb093AlphaDummy119 r))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_124`. -/
@[expose]
noncomputable def nb093AlphaDummy124 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb093AlphaDummy115 A)))).fv ∪
      ((synCcompl (Class.cv (nb093AlphaDummy116 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_125`. -/
@[expose]
noncomputable def nb093AlphaDummy125 (r : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb093AlphaDummy118 r)))).fv ∪
      ((synCcompl (Class.cv (nb093AlphaDummy119 r)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_126`. -/
@[expose]
noncomputable def nb093AlphaDummy126 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy115 A))).fv ∪
      ((Class.cv (nb093AlphaDummy115 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_127`. -/
@[expose]
noncomputable def nb093AlphaDummy127 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy118 r))).fv ∪
      ((Class.cv (nb093AlphaDummy118 r))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_128`. -/
@[expose]
noncomputable def nb093AlphaDummy128 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy116 A))).fv ∪
      ((Class.cv (nb093AlphaDummy116 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_129`. -/
@[expose]
noncomputable def nb093AlphaDummy129 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy119 r))).fv ∪
      ((Class.cv (nb093AlphaDummy119 r))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_130`. -/
@[expose]
noncomputable def nb093AlphaDummy130 (A : Class) : Var :=
  (freshVar (((Class.cab (nb093AlphaDummy100 A)
          (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy058 A))
            (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
              (synCun (synCphi (Class.cv (nb093AlphaDummy101 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy100 A)
          (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy058 A))
            (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
              (synCun (synCphi (Class.cv (nb093AlphaDummy101 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_131`. -/
@[expose]
noncomputable def nb093AlphaDummy131 (r : Var) : Var :=
  (freshVar (((Class.cab (nb093AlphaDummy102 r)
          (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy060 r))
            (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
              (synCun (synCphi (Class.cv (nb093AlphaDummy103 r)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy102 r)
          (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy060 r))
            (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
              (synCun (synCphi (Class.cv (nb093AlphaDummy103 r)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_132`. -/
@[expose]
noncomputable def nb093AlphaDummy132 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb093AlphaDummy101 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_133`. -/
@[expose]
noncomputable def nb093AlphaDummy133 (r : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb093AlphaDummy103 r))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_134`. -/
@[expose]
noncomputable def nb093AlphaDummy134 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb093AlphaDummy101 A)))).fv ∪
      ((synCphi (Class.cv (nb093AlphaDummy101 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_135`. -/
@[expose]
noncomputable def nb093AlphaDummy135 (r : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb093AlphaDummy103 r)))).fv ∪
      ((synCphi (Class.cv (nb093AlphaDummy103 r)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_136`. -/
@[expose]
noncomputable def nb093AlphaDummy136 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy045 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_137`. -/
@[expose]
noncomputable def nb093AlphaDummy137 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy045 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_138`. -/
@[expose]
noncomputable def nb093AlphaDummy138 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy047 r d))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_139`. -/
@[expose]
noncomputable def nb093AlphaDummy139 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy047 r d))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_140`. -/
@[expose]
noncomputable def nb093AlphaDummy140 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb093AlphaDummy136 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb093AlphaDummy136 A)) (synC1c))).fv ∪
      ((Class.cv (nb093AlphaDummy136 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_141`. -/
@[expose]
noncomputable def nb093AlphaDummy141 (r : Var) (d : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb093AlphaDummy138 r d)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb093AlphaDummy138 r d)) (synC1c))).fv ∪
      ((Class.cv (nb093AlphaDummy138 r d))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_142`. -/
@[expose]
noncomputable def nb093AlphaDummy142 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy136 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_143`. -/
@[expose]
noncomputable def nb093AlphaDummy143 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy136 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_144`. -/
@[expose]
noncomputable def nb093AlphaDummy144 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy136 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_145`. -/
@[expose]
noncomputable def nb093AlphaDummy145 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_146`. -/
@[expose]
noncomputable def nb093AlphaDummy146 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_147`. -/
@[expose]
noncomputable def nb093AlphaDummy147 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_148`. -/
@[expose]
noncomputable def nb093AlphaDummy148 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb093AlphaDummy143 A))
          (Class.cv (nb093AlphaDummy144 A)))).fv ∪
      ((synCnin (Class.cv (nb093AlphaDummy143 A)) (Class.cv (nb093AlphaDummy144 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_149`. -/
@[expose]
noncomputable def nb093AlphaDummy149 (r : Var) (d : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb093AlphaDummy146 r d))
          (Class.cv (nb093AlphaDummy147 r d)))).fv ∪
      ((synCnin (Class.cv (nb093AlphaDummy146 r d))
          (Class.cv (nb093AlphaDummy147 r d)))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


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

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_150`. -/
@[expose]
noncomputable def nb093AlphaDummy150 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy143 A))).fv ∪
      ((Class.cv (nb093AlphaDummy144 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_151`. -/
@[expose]
noncomputable def nb093AlphaDummy151 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy146 r d))).fv ∪
      ((Class.cv (nb093AlphaDummy147 r d))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_152`. -/
@[expose]
noncomputable def nb093AlphaDummy152 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb093AlphaDummy143 A)))).fv ∪
      ((synCcompl (Class.cv (nb093AlphaDummy144 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_153`. -/
@[expose]
noncomputable def nb093AlphaDummy153 (r : Var) (d : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb093AlphaDummy146 r d)))).fv ∪
      ((synCcompl (Class.cv (nb093AlphaDummy147 r d)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_154`. -/
@[expose]
noncomputable def nb093AlphaDummy154 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy143 A))).fv ∪
      ((Class.cv (nb093AlphaDummy143 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_155`. -/
@[expose]
noncomputable def nb093AlphaDummy155 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy146 r d))).fv ∪
      ((Class.cv (nb093AlphaDummy146 r d))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_156`. -/
@[expose]
noncomputable def nb093AlphaDummy156 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy144 A))).fv ∪
      ((Class.cv (nb093AlphaDummy144 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_157`. -/
@[expose]
noncomputable def nb093AlphaDummy157 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy147 r d))).fv ∪
      ((Class.cv (nb093AlphaDummy147 r d))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_158`. -/
@[expose]
noncomputable def nb093AlphaDummy158 (A : Class) : Var :=
  (freshVar (((Class.cab (nb093AlphaDummy044 A)
          (synWrex (nb093AlphaDummy045 A) (Class.cv (nb093AlphaDummy000 A))
            (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
              (synCun (synCphi (Class.cv (nb093AlphaDummy045 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy044 A)
          (synWrex (nb093AlphaDummy045 A) (Class.cv (nb093AlphaDummy000 A))
            (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
              (synCun (synCphi (Class.cv (nb093AlphaDummy045 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_159`. -/
@[expose]
noncomputable def nb093AlphaDummy159 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cab (nb093AlphaDummy046 r d)
          (synWrex (nb093AlphaDummy047 r d) (Class.cv d)
            (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
              (synCun (synCphi (Class.cv (nb093AlphaDummy047 r d)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy046 r d)
          (synWrex (nb093AlphaDummy047 r d) (Class.cv d)
            (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
              (synCun (synCphi (Class.cv (nb093AlphaDummy047 r d)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_160`. -/
@[expose]
noncomputable def nb093AlphaDummy160 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb093AlphaDummy045 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_161`. -/
@[expose]
noncomputable def nb093AlphaDummy161 (r : Var) (d : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb093AlphaDummy047 r d))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_162`. -/
@[expose]
noncomputable def nb093AlphaDummy162 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb093AlphaDummy045 A)))).fv ∪
      ((synCphi (Class.cv (nb093AlphaDummy045 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_163`. -/
@[expose]
noncomputable def nb093AlphaDummy163 (r : Var) (d : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb093AlphaDummy047 r d)))).fv ∪
      ((synCphi (Class.cv (nb093AlphaDummy047 r d)))).fv) 0)

theorem nb093_fresh_000 (A : Class) :
    (nb093AlphaDummy038 A) ∉
      (((Class.cab (nb093AlphaDummy008 A)
            (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy009 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy008 A)
            (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy009 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb093AlphaDummy038] using
    freshVar_not_mem
      (((Class.cab (nb093AlphaDummy008 A)
            (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy009 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy008 A)
            (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy009 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb093_fresh_001 (A : Class) :
    (nb093AlphaDummy014 A) ∉
      (((Class.cab (nb093AlphaDummy008 A)
            (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                (synCphi (Class.cv (nb093AlphaDummy009 A))))))).fv ∪
        ((Class.cab (nb093AlphaDummy008 A)
            (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                (synCphi (Class.cv (nb093AlphaDummy009 A))))))).fv) :=
  by
  simpa only [nb093AlphaDummy014] using
    freshVar_not_mem
      (((Class.cab (nb093AlphaDummy008 A)
            (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                (synCphi (Class.cv (nb093AlphaDummy009 A))))))).fv ∪
        ((Class.cab (nb093AlphaDummy008 A)
            (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                (synCphi (Class.cv (nb093AlphaDummy009 A))))))).fv)
      0

theorem nb093_fresh_002 (r : Var) (d : Var) :
    (nb093AlphaDummy039 r d) ∉
      (((Class.cab (nb093AlphaDummy010 r d)
            (synWrex (nb093AlphaDummy011 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                (synCun (synCphi (Class.cv (nb093AlphaDummy011 r d)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy010 r d)
            (synWrex (nb093AlphaDummy011 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                (synCun (synCphi (Class.cv (nb093AlphaDummy011 r d)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb093AlphaDummy039] using
    freshVar_not_mem
      (((Class.cab (nb093AlphaDummy010 r d)
            (synWrex (nb093AlphaDummy011 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                (synCun (synCphi (Class.cv (nb093AlphaDummy011 r d)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy010 r d)
            (synWrex (nb093AlphaDummy011 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                (synCun (synCphi (Class.cv (nb093AlphaDummy011 r d)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb093_fresh_003 (r : Var) (d : Var) :
    (nb093AlphaDummy015 r d) ∉
      (((Class.cab (nb093AlphaDummy010 r d)
            (synWrex (nb093AlphaDummy011 r d) (Class.cv r)
              (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                (synCphi (Class.cv (nb093AlphaDummy011 r d))))))).fv ∪
        ((Class.cab (nb093AlphaDummy010 r d)
            (synWrex (nb093AlphaDummy011 r d) (Class.cv r)
              (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                (synCphi (Class.cv (nb093AlphaDummy011 r d))))))).fv) :=
  by
  simpa only [nb093AlphaDummy015] using
    freshVar_not_mem
      (((Class.cab (nb093AlphaDummy010 r d)
            (synWrex (nb093AlphaDummy011 r d) (Class.cv r)
              (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                (synCphi (Class.cv (nb093AlphaDummy011 r d))))))).fv ∪
        ((Class.cab (nb093AlphaDummy010 r d)
            (synWrex (nb093AlphaDummy011 r d) (Class.cv r)
              (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                (synCphi (Class.cv (nb093AlphaDummy011 r d))))))).fv)
      0

theorem nb093_fresh_004 (A : Class) :
    (nb093AlphaDummy158 A) ∉
      (((Class.cab (nb093AlphaDummy044 A)
            (synWrex (nb093AlphaDummy045 A) (Class.cv (nb093AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy045 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy044 A)
            (synWrex (nb093AlphaDummy045 A) (Class.cv (nb093AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy045 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb093AlphaDummy158] using
    freshVar_not_mem
      (((Class.cab (nb093AlphaDummy044 A)
            (synWrex (nb093AlphaDummy045 A) (Class.cv (nb093AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy045 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy044 A)
            (synWrex (nb093AlphaDummy045 A) (Class.cv (nb093AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy045 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb093_fresh_005 (A : Class) :
    (nb093AlphaDummy050 A) ∉
      (((Class.cab (nb093AlphaDummy044 A) (synWrex (nb093AlphaDummy045 A)
              (synCdif (Class.cv (nb093AlphaDummy001 A))
                (synCcnv (Class.cv (nb093AlphaDummy001 A))))
              (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                (synCphi (Class.cv (nb093AlphaDummy045 A))))))).fv ∪
        ((Class.cab (nb093AlphaDummy044 A) (synWrex (nb093AlphaDummy045 A)
              (synCdif (Class.cv (nb093AlphaDummy001 A))
                (synCcnv (Class.cv (nb093AlphaDummy001 A))))
              (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                (synCphi (Class.cv (nb093AlphaDummy045 A))))))).fv) :=
  by
  simpa only [nb093AlphaDummy050] using
    freshVar_not_mem
      (((Class.cab (nb093AlphaDummy044 A) (synWrex (nb093AlphaDummy045 A)
              (synCdif (Class.cv (nb093AlphaDummy001 A))
                (synCcnv (Class.cv (nb093AlphaDummy001 A))))
              (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                (synCphi (Class.cv (nb093AlphaDummy045 A))))))).fv ∪
        ((Class.cab (nb093AlphaDummy044 A) (synWrex (nb093AlphaDummy045 A)
              (synCdif (Class.cv (nb093AlphaDummy001 A))
                (synCcnv (Class.cv (nb093AlphaDummy001 A))))
              (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                (synCphi (Class.cv (nb093AlphaDummy045 A))))))).fv)
      0

theorem nb093_fresh_006 (r : Var) (d : Var) :
    (nb093AlphaDummy159 r d) ∉
      (((Class.cab (nb093AlphaDummy046 r d)
            (synWrex (nb093AlphaDummy047 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                (synCun (synCphi (Class.cv (nb093AlphaDummy047 r d)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy046 r d)
            (synWrex (nb093AlphaDummy047 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                (synCun (synCphi (Class.cv (nb093AlphaDummy047 r d)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb093AlphaDummy159] using
    freshVar_not_mem
      (((Class.cab (nb093AlphaDummy046 r d)
            (synWrex (nb093AlphaDummy047 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                (synCun (synCphi (Class.cv (nb093AlphaDummy047 r d)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy046 r d)
            (synWrex (nb093AlphaDummy047 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                (synCun (synCphi (Class.cv (nb093AlphaDummy047 r d)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb093_fresh_007 (r : Var) (d : Var) :
    (nb093AlphaDummy051 r d) ∉
      (((Class.cab (nb093AlphaDummy046 r d) (synWrex (nb093AlphaDummy047 r d)
              (synCdif (Class.cv r) (synCcnv (Class.cv r)))
              (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                (synCphi (Class.cv (nb093AlphaDummy047 r d))))))).fv ∪
        ((Class.cab (nb093AlphaDummy046 r d) (synWrex (nb093AlphaDummy047 r d)
              (synCdif (Class.cv r) (synCcnv (Class.cv r)))
              (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                (synCphi (Class.cv (nb093AlphaDummy047 r d))))))).fv) :=
  by
  simpa only [nb093AlphaDummy051] using
    freshVar_not_mem
      (((Class.cab (nb093AlphaDummy046 r d) (synWrex (nb093AlphaDummy047 r d)
              (synCdif (Class.cv r) (synCcnv (Class.cv r)))
              (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                (synCphi (Class.cv (nb093AlphaDummy047 r d))))))).fv ∪
        ((Class.cab (nb093AlphaDummy046 r d) (synWrex (nb093AlphaDummy047 r d)
              (synCdif (Class.cv r) (synCcnv (Class.cv r)))
              (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                (synCphi (Class.cv (nb093AlphaDummy047 r d))))))).fv)
      0

theorem nb093_fresh_008 (A : Class) :
    (nb093AlphaDummy070 A) ∉
      (((Class.cab (nb093AlphaDummy064 A)
            (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy058 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                (synCphi (Class.cv (nb093AlphaDummy065 A))))))).fv ∪
        ((Class.cab (nb093AlphaDummy064 A)
            (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy058 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                (synCphi (Class.cv (nb093AlphaDummy065 A))))))).fv) :=
  by
  simpa only [nb093AlphaDummy070] using
    freshVar_not_mem
      (((Class.cab (nb093AlphaDummy064 A)
            (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy058 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                (synCphi (Class.cv (nb093AlphaDummy065 A))))))).fv ∪
        ((Class.cab (nb093AlphaDummy064 A)
            (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy058 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                (synCphi (Class.cv (nb093AlphaDummy065 A))))))).fv)
      0

theorem nb093_fresh_009 (A : Class) :
    (nb093AlphaDummy094 A) ∉
      (((Class.cab (nb093AlphaDummy064 A)
            (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy059 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy065 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy064 A)
            (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy059 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy065 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb093AlphaDummy094] using
    freshVar_not_mem
      (((Class.cab (nb093AlphaDummy064 A)
            (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy059 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy065 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy064 A)
            (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy059 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy065 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb093_fresh_010 (r : Var) :
    (nb093AlphaDummy071 r) ∉
      (((Class.cab (nb093AlphaDummy066 r)
            (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy060 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                (synCphi (Class.cv (nb093AlphaDummy067 r))))))).fv ∪
        ((Class.cab (nb093AlphaDummy066 r)
            (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy060 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                (synCphi (Class.cv (nb093AlphaDummy067 r))))))).fv) :=
  by
  simpa only [nb093AlphaDummy071] using
    freshVar_not_mem
      (((Class.cab (nb093AlphaDummy066 r)
            (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy060 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                (synCphi (Class.cv (nb093AlphaDummy067 r))))))).fv ∪
        ((Class.cab (nb093AlphaDummy066 r)
            (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy060 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                (synCphi (Class.cv (nb093AlphaDummy067 r))))))).fv)
      0

theorem nb093_fresh_011 (r : Var) :
    (nb093AlphaDummy095 r) ∉
      (((Class.cab (nb093AlphaDummy066 r)
            (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy061 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                (synCun (synCphi (Class.cv (nb093AlphaDummy067 r)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy066 r)
            (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy061 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                (synCun (synCphi (Class.cv (nb093AlphaDummy067 r)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb093AlphaDummy095] using
    freshVar_not_mem
      (((Class.cab (nb093AlphaDummy066 r)
            (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy061 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                (synCun (synCphi (Class.cv (nb093AlphaDummy067 r)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy066 r)
            (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy061 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                (synCun (synCphi (Class.cv (nb093AlphaDummy067 r)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb093_fresh_012 (A : Class) :
    (nb093AlphaDummy130 A) ∉
      (((Class.cab (nb093AlphaDummy100 A)
            (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy058 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy101 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy100 A)
            (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy058 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy101 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb093AlphaDummy130] using
    freshVar_not_mem
      (((Class.cab (nb093AlphaDummy100 A)
            (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy058 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy101 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy100 A)
            (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy058 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy101 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb093_fresh_013 (A : Class) :
    (nb093AlphaDummy106 A) ∉
      (((Class.cab (nb093AlphaDummy100 A)
            (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy059 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                (synCphi (Class.cv (nb093AlphaDummy101 A))))))).fv ∪
        ((Class.cab (nb093AlphaDummy100 A)
            (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy059 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                (synCphi (Class.cv (nb093AlphaDummy101 A))))))).fv) :=
  by
  simpa only [nb093AlphaDummy106] using
    freshVar_not_mem
      (((Class.cab (nb093AlphaDummy100 A)
            (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy059 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                (synCphi (Class.cv (nb093AlphaDummy101 A))))))).fv ∪
        ((Class.cab (nb093AlphaDummy100 A)
            (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy059 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                (synCphi (Class.cv (nb093AlphaDummy101 A))))))).fv)
      0

theorem nb093_fresh_014 (r : Var) :
    (nb093AlphaDummy131 r) ∉
      (((Class.cab (nb093AlphaDummy102 r)
            (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy060 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                (synCun (synCphi (Class.cv (nb093AlphaDummy103 r)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy102 r)
            (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy060 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                (synCun (synCphi (Class.cv (nb093AlphaDummy103 r)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb093AlphaDummy131] using
    freshVar_not_mem
      (((Class.cab (nb093AlphaDummy102 r)
            (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy060 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                (synCun (synCphi (Class.cv (nb093AlphaDummy103 r)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy102 r)
            (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy060 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                (synCun (synCphi (Class.cv (nb093AlphaDummy103 r)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb093_fresh_015 (r : Var) :
    (nb093AlphaDummy107 r) ∉
      (((Class.cab (nb093AlphaDummy102 r)
            (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy061 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                (synCphi (Class.cv (nb093AlphaDummy103 r))))))).fv ∪
        ((Class.cab (nb093AlphaDummy102 r)
            (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy061 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                (synCphi (Class.cv (nb093AlphaDummy103 r))))))).fv) :=
  by
  simpa only [nb093AlphaDummy107] using
    freshVar_not_mem
      (((Class.cab (nb093AlphaDummy102 r)
            (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy061 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                (synCphi (Class.cv (nb093AlphaDummy103 r))))))).fv ∪
        ((Class.cab (nb093AlphaDummy102 r)
            (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy061 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                (synCphi (Class.cv (nb093AlphaDummy103 r))))))).fv)
      0

theorem nb093_fresh_016 (A : Class) :
    (nb093AlphaDummy058 A) ∉ (((Class.cv (nb093AlphaDummy001 A))).fv) := by
  simpa only [nb093AlphaDummy058] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy001 A))).fv) 0

theorem nb093_fresh_017 (A : Class) :
    (nb093AlphaDummy059 A) ∉ (((Class.cv (nb093AlphaDummy001 A))).fv) := by
  simpa only [nb093AlphaDummy059] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy001 A))).fv) 1

theorem nb093_distinct_018 (A : Class) :
    (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy059 A) := by
  simpa only [nb093AlphaDummy058, nb093AlphaDummy059] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy001 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb093_fresh_019 (A : Class) :
    (nb093AlphaDummy008 A) ∉
      (((Class.cv (nb093AlphaDummy001 A))).fv ∪ ((Class.cv (nb093AlphaDummy000 A))).fv) :=
  by
  simpa only [nb093AlphaDummy008] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy001 A))).fv ∪ ((Class.cv (nb093AlphaDummy000 A))).fv)
      0

theorem nb093_fresh_020 (A : Class) :
    (nb093AlphaDummy009 A) ∉
      (((Class.cv (nb093AlphaDummy001 A))).fv ∪ ((Class.cv (nb093AlphaDummy000 A))).fv) :=
  by
  simpa only [nb093AlphaDummy009] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy001 A))).fv ∪ ((Class.cv (nb093AlphaDummy000 A))).fv)
      1

theorem nb093_distinct_021 (A : Class) :
    (nb093AlphaDummy008 A) ≠ (nb093AlphaDummy009 A) := by
  simpa only [nb093AlphaDummy008, nb093AlphaDummy009] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy001 A))).fv ∪
        ((Class.cv (nb093AlphaDummy000 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb093_fresh_022 (A : Class) :
    (nb093AlphaDummy054 A) ∉
      (((Class.cv (nb093AlphaDummy001 A))).fv ∪
        ((synCcompl (synCcnv (Class.cv (nb093AlphaDummy001 A))))).fv) :=
  by
  simpa only [nb093AlphaDummy054] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy001 A))).fv ∪
        ((synCcompl (synCcnv (Class.cv (nb093AlphaDummy001 A))))).fv)
      0

theorem nb093_fresh_023 (A : Class) :
    (nb093AlphaDummy016 A) ∉ (((Class.cv (nb093AlphaDummy009 A))).fv) := by
  simpa only [nb093AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy009 A))).fv) 0

theorem nb093_fresh_024 (A : Class) :
    (nb093AlphaDummy017 A) ∉ (((Class.cv (nb093AlphaDummy009 A))).fv) := by
  simpa only [nb093AlphaDummy017] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy009 A))).fv) 1

theorem nb093_distinct_025 (A : Class) :
    (nb093AlphaDummy016 A) ≠ (nb093AlphaDummy017 A) := by
  simpa only [nb093AlphaDummy016, nb093AlphaDummy017] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy009 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb093_fresh_026 (r : Var) (d : Var) :
    (nb093AlphaDummy018 r d) ∉ (((Class.cv (nb093AlphaDummy011 r d))).fv) := by
  simpa only [nb093AlphaDummy018] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy011 r d))).fv) 0

theorem nb093_fresh_027 (r : Var) (d : Var) :
    (nb093AlphaDummy019 r d) ∉ (((Class.cv (nb093AlphaDummy011 r d))).fv) := by
  simpa only [nb093AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy011 r d))).fv) 1

theorem nb093_distinct_028 (r : Var) (d : Var) :
    (nb093AlphaDummy018 r d) ≠ (nb093AlphaDummy019 r d) := by
  simpa only [nb093AlphaDummy018, nb093AlphaDummy019] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy011 r d))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb093_fresh_029 (A : Class) :
    (nb093AlphaDummy022 A) ∉
      (((Class.cv (nb093AlphaDummy016 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy016 A))).fv ∪ ((synC1c)).fv) 0

theorem nb093_fresh_030 (A : Class) :
    (nb093AlphaDummy023 A) ∉
      (((Class.cv (nb093AlphaDummy016 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy016 A))).fv ∪ ((synC1c)).fv) 1

theorem nb093_fresh_031 (A : Class) :
    (nb093AlphaDummy024 A) ∉
      (((Class.cv (nb093AlphaDummy016 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy016 A))).fv ∪ ((synC1c)).fv) 2

theorem nb093_distinct_032 (A : Class) :
    (nb093AlphaDummy022 A) ≠ (nb093AlphaDummy023 A) := by
  simpa only [nb093AlphaDummy022, nb093AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy016 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb093_distinct_033 (A : Class) :
    (nb093AlphaDummy022 A) ≠ (nb093AlphaDummy024 A) := by
  simpa only [nb093AlphaDummy022, nb093AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy016 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb093_distinct_034 (A : Class) :
    (nb093AlphaDummy023 A) ≠ (nb093AlphaDummy024 A) := by
  simpa only [nb093AlphaDummy023, nb093AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy016 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb093_fresh_035 (r : Var) (d : Var) :
    (nb093AlphaDummy025 r d) ∉
      (((Class.cv (nb093AlphaDummy018 r d))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy018 r d))).fv ∪ ((synC1c)).fv) 0

theorem nb093_fresh_036 (r : Var) (d : Var) :
    (nb093AlphaDummy026 r d) ∉
      (((Class.cv (nb093AlphaDummy018 r d))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy026] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy018 r d))).fv ∪ ((synC1c)).fv) 1

theorem nb093_fresh_037 (r : Var) (d : Var) :
    (nb093AlphaDummy027 r d) ∉
      (((Class.cv (nb093AlphaDummy018 r d))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy027] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy018 r d))).fv ∪ ((synC1c)).fv) 2

theorem nb093_distinct_038 (r : Var) (d : Var) :
    (nb093AlphaDummy025 r d) ≠ (nb093AlphaDummy026 r d) := by
  simpa only [nb093AlphaDummy025, nb093AlphaDummy026] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb093_distinct_039 (r : Var) (d : Var) :
    (nb093AlphaDummy025 r d) ≠ (nb093AlphaDummy027 r d) := by
  simpa only [nb093AlphaDummy025, nb093AlphaDummy027] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb093_distinct_040 (r : Var) (d : Var) :
    (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy027 r d) := by
  simpa only [nb093AlphaDummy026, nb093AlphaDummy027] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb093_fresh_041 (A : Class) :
    (nb093AlphaDummy034 A) ∉
      (((Class.cv (nb093AlphaDummy023 A))).fv ∪ ((Class.cv (nb093AlphaDummy023 A))).fv) :=
  by
  simpa only [nb093AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy023 A))).fv ∪ ((Class.cv (nb093AlphaDummy023 A))).fv)
      0

theorem nb093_fresh_042 (A : Class) :
    (nb093AlphaDummy030 A) ∉
      (((Class.cv (nb093AlphaDummy023 A))).fv ∪ ((Class.cv (nb093AlphaDummy024 A))).fv) :=
  by
  simpa only [nb093AlphaDummy030] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy023 A))).fv ∪ ((Class.cv (nb093AlphaDummy024 A))).fv)
      0

theorem nb093_fresh_043 (A : Class) :
    (nb093AlphaDummy036 A) ∉
      (((Class.cv (nb093AlphaDummy024 A))).fv ∪ ((Class.cv (nb093AlphaDummy024 A))).fv) :=
  by
  simpa only [nb093AlphaDummy036] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy024 A))).fv ∪ ((Class.cv (nb093AlphaDummy024 A))).fv)
      0

theorem nb093_fresh_044 (r : Var) (d : Var) :
    (nb093AlphaDummy035 r d) ∉
      (((Class.cv (nb093AlphaDummy026 r d))).fv ∪
        ((Class.cv (nb093AlphaDummy026 r d))).fv) :=
  by
  simpa only [nb093AlphaDummy035] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy026 r d))).fv ∪
        ((Class.cv (nb093AlphaDummy026 r d))).fv)
      0

theorem nb093_fresh_045 (r : Var) (d : Var) :
    (nb093AlphaDummy031 r d) ∉
      (((Class.cv (nb093AlphaDummy026 r d))).fv ∪
        ((Class.cv (nb093AlphaDummy027 r d))).fv) :=
  by
  simpa only [nb093AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy026 r d))).fv ∪
        ((Class.cv (nb093AlphaDummy027 r d))).fv)
      0

theorem nb093_fresh_046 (r : Var) (d : Var) :
    (nb093AlphaDummy037 r d) ∉
      (((Class.cv (nb093AlphaDummy027 r d))).fv ∪
        ((Class.cv (nb093AlphaDummy027 r d))).fv) :=
  by
  simpa only [nb093AlphaDummy037] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy027 r d))).fv ∪
        ((Class.cv (nb093AlphaDummy027 r d))).fv)
      0

theorem nb093_fresh_047 (A : Class) :
    (nb093AlphaDummy136 A) ∉ (((Class.cv (nb093AlphaDummy045 A))).fv) := by
  simpa only [nb093AlphaDummy136] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy045 A))).fv) 0

theorem nb093_fresh_048 (A : Class) :
    (nb093AlphaDummy137 A) ∉ (((Class.cv (nb093AlphaDummy045 A))).fv) := by
  simpa only [nb093AlphaDummy137] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy045 A))).fv) 1

theorem nb093_distinct_049 (A : Class) :
    (nb093AlphaDummy136 A) ≠ (nb093AlphaDummy137 A) := by
  simpa only [nb093AlphaDummy136, nb093AlphaDummy137] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy045 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb093_fresh_050 (r : Var) (d : Var) :
    (nb093AlphaDummy138 r d) ∉ (((Class.cv (nb093AlphaDummy047 r d))).fv) := by
  simpa only [nb093AlphaDummy138] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy047 r d))).fv) 0

theorem nb093_fresh_051 (r : Var) (d : Var) :
    (nb093AlphaDummy139 r d) ∉ (((Class.cv (nb093AlphaDummy047 r d))).fv) := by
  simpa only [nb093AlphaDummy139] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy047 r d))).fv) 1

theorem nb093_distinct_052 (r : Var) (d : Var) :
    (nb093AlphaDummy138 r d) ≠ (nb093AlphaDummy139 r d) := by
  simpa only [nb093AlphaDummy138, nb093AlphaDummy139] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy047 r d))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb093_fresh_053 (A : Class) :
    (nb093AlphaDummy064 A) ∉
      (((Class.cv (nb093AlphaDummy058 A))).fv ∪ ((Class.cv (nb093AlphaDummy059 A))).fv) :=
  by
  simpa only [nb093AlphaDummy064] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy058 A))).fv ∪ ((Class.cv (nb093AlphaDummy059 A))).fv)
      0

theorem nb093_fresh_054 (A : Class) :
    (nb093AlphaDummy065 A) ∉
      (((Class.cv (nb093AlphaDummy058 A))).fv ∪ ((Class.cv (nb093AlphaDummy059 A))).fv) :=
  by
  simpa only [nb093AlphaDummy065] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy058 A))).fv ∪ ((Class.cv (nb093AlphaDummy059 A))).fv)
      1

theorem nb093_distinct_055 (A : Class) :
    (nb093AlphaDummy064 A) ≠ (nb093AlphaDummy065 A) := by
  simpa only [nb093AlphaDummy064, nb093AlphaDummy065] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy058 A))).fv ∪
        ((Class.cv (nb093AlphaDummy059 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb093_fresh_056 (A : Class) :
    (nb093AlphaDummy100 A) ∉
      (((Class.cv (nb093AlphaDummy059 A))).fv ∪ ((Class.cv (nb093AlphaDummy058 A))).fv) :=
  by
  simpa only [nb093AlphaDummy100] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy059 A))).fv ∪ ((Class.cv (nb093AlphaDummy058 A))).fv)
      0

theorem nb093_fresh_057 (A : Class) :
    (nb093AlphaDummy101 A) ∉
      (((Class.cv (nb093AlphaDummy059 A))).fv ∪ ((Class.cv (nb093AlphaDummy058 A))).fv) :=
  by
  simpa only [nb093AlphaDummy101] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy059 A))).fv ∪ ((Class.cv (nb093AlphaDummy058 A))).fv)
      1

theorem nb093_distinct_058 (A : Class) :
    (nb093AlphaDummy100 A) ≠ (nb093AlphaDummy101 A) := by
  simpa only [nb093AlphaDummy100, nb093AlphaDummy101] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy059 A))).fv ∪
        ((Class.cv (nb093AlphaDummy058 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb093_fresh_059 (r : Var) :
    (nb093AlphaDummy066 r) ∉
      (((Class.cv (nb093AlphaDummy060 r))).fv ∪ ((Class.cv (nb093AlphaDummy061 r))).fv) :=
  by
  simpa only [nb093AlphaDummy066] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy060 r))).fv ∪ ((Class.cv (nb093AlphaDummy061 r))).fv)
      0

theorem nb093_fresh_060 (r : Var) :
    (nb093AlphaDummy067 r) ∉
      (((Class.cv (nb093AlphaDummy060 r))).fv ∪ ((Class.cv (nb093AlphaDummy061 r))).fv) :=
  by
  simpa only [nb093AlphaDummy067] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy060 r))).fv ∪ ((Class.cv (nb093AlphaDummy061 r))).fv)
      1

theorem nb093_distinct_061 (r : Var) :
    (nb093AlphaDummy066 r) ≠ (nb093AlphaDummy067 r) := by
  simpa only [nb093AlphaDummy066, nb093AlphaDummy067] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy060 r))).fv ∪
        ((Class.cv (nb093AlphaDummy061 r))).fv) (i := 0) (j := 1) (by decide))

theorem nb093_fresh_062 (r : Var) :
    (nb093AlphaDummy102 r) ∉
      (((Class.cv (nb093AlphaDummy061 r))).fv ∪ ((Class.cv (nb093AlphaDummy060 r))).fv) :=
  by
  simpa only [nb093AlphaDummy102] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy061 r))).fv ∪ ((Class.cv (nb093AlphaDummy060 r))).fv)
      0

theorem nb093_fresh_063 (r : Var) :
    (nb093AlphaDummy103 r) ∉
      (((Class.cv (nb093AlphaDummy061 r))).fv ∪ ((Class.cv (nb093AlphaDummy060 r))).fv) :=
  by
  simpa only [nb093AlphaDummy103] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy061 r))).fv ∪ ((Class.cv (nb093AlphaDummy060 r))).fv)
      1

theorem nb093_distinct_064 (r : Var) :
    (nb093AlphaDummy102 r) ≠ (nb093AlphaDummy103 r) := by
  simpa only [nb093AlphaDummy102, nb093AlphaDummy103] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy061 r))).fv ∪
        ((Class.cv (nb093AlphaDummy060 r))).fv) (i := 0) (j := 1) (by decide))

theorem nb093_fresh_065 (A : Class) :
    (nb093AlphaDummy072 A) ∉ (((Class.cv (nb093AlphaDummy065 A))).fv) := by
  simpa only [nb093AlphaDummy072] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy065 A))).fv) 0

theorem nb093_fresh_066 (A : Class) :
    (nb093AlphaDummy073 A) ∉ (((Class.cv (nb093AlphaDummy065 A))).fv) := by
  simpa only [nb093AlphaDummy073] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy065 A))).fv) 1

theorem nb093_distinct_067 (A : Class) :
    (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy073 A) := by
  simpa only [nb093AlphaDummy072, nb093AlphaDummy073] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy065 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb093_fresh_068 (r : Var) :
    (nb093AlphaDummy074 r) ∉ (((Class.cv (nb093AlphaDummy067 r))).fv) := by
  simpa only [nb093AlphaDummy074] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy067 r))).fv) 0

theorem nb093_fresh_069 (r : Var) :
    (nb093AlphaDummy075 r) ∉ (((Class.cv (nb093AlphaDummy067 r))).fv) := by
  simpa only [nb093AlphaDummy075] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy067 r))).fv) 1

theorem nb093_distinct_070 (r : Var) :
    (nb093AlphaDummy074 r) ≠ (nb093AlphaDummy075 r) := by
  simpa only [nb093AlphaDummy074, nb093AlphaDummy075] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy067 r))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb093_fresh_071 (A : Class) :
    (nb093AlphaDummy078 A) ∉
      (((Class.cv (nb093AlphaDummy072 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy078] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy072 A))).fv ∪ ((synC1c)).fv) 0

theorem nb093_fresh_072 (A : Class) :
    (nb093AlphaDummy079 A) ∉
      (((Class.cv (nb093AlphaDummy072 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy079] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy072 A))).fv ∪ ((synC1c)).fv) 1

theorem nb093_fresh_073 (A : Class) :
    (nb093AlphaDummy080 A) ∉
      (((Class.cv (nb093AlphaDummy072 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy080] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy072 A))).fv ∪ ((synC1c)).fv) 2

theorem nb093_distinct_074 (A : Class) :
    (nb093AlphaDummy078 A) ≠ (nb093AlphaDummy079 A) := by
  simpa only [nb093AlphaDummy078, nb093AlphaDummy079] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy072 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb093_distinct_075 (A : Class) :
    (nb093AlphaDummy078 A) ≠ (nb093AlphaDummy080 A) := by
  simpa only [nb093AlphaDummy078, nb093AlphaDummy080] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy072 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb093_distinct_076 (A : Class) :
    (nb093AlphaDummy079 A) ≠ (nb093AlphaDummy080 A) := by
  simpa only [nb093AlphaDummy079, nb093AlphaDummy080] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy072 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb093_fresh_077 (r : Var) :
    (nb093AlphaDummy081 r) ∉
      (((Class.cv (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy081] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) 0

theorem nb093_fresh_078 (r : Var) :
    (nb093AlphaDummy082 r) ∉
      (((Class.cv (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy082] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) 1

theorem nb093_fresh_079 (r : Var) :
    (nb093AlphaDummy083 r) ∉
      (((Class.cv (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy083] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) 2

theorem nb093_distinct_080 (r : Var) :
    (nb093AlphaDummy081 r) ≠ (nb093AlphaDummy082 r) := by
  simpa only [nb093AlphaDummy081, nb093AlphaDummy082] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb093_distinct_081 (r : Var) :
    (nb093AlphaDummy081 r) ≠ (nb093AlphaDummy083 r) := by
  simpa only [nb093AlphaDummy081, nb093AlphaDummy083] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb093_distinct_082 (r : Var) :
    (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy083 r) := by
  simpa only [nb093AlphaDummy082, nb093AlphaDummy083] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb093_fresh_083 (A : Class) :
    (nb093AlphaDummy090 A) ∉
      (((Class.cv (nb093AlphaDummy079 A))).fv ∪ ((Class.cv (nb093AlphaDummy079 A))).fv) :=
  by
  simpa only [nb093AlphaDummy090] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy079 A))).fv ∪ ((Class.cv (nb093AlphaDummy079 A))).fv)
      0

theorem nb093_fresh_084 (A : Class) :
    (nb093AlphaDummy086 A) ∉
      (((Class.cv (nb093AlphaDummy079 A))).fv ∪ ((Class.cv (nb093AlphaDummy080 A))).fv) :=
  by
  simpa only [nb093AlphaDummy086] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy079 A))).fv ∪ ((Class.cv (nb093AlphaDummy080 A))).fv)
      0

theorem nb093_fresh_085 (A : Class) :
    (nb093AlphaDummy092 A) ∉
      (((Class.cv (nb093AlphaDummy080 A))).fv ∪ ((Class.cv (nb093AlphaDummy080 A))).fv) :=
  by
  simpa only [nb093AlphaDummy092] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy080 A))).fv ∪ ((Class.cv (nb093AlphaDummy080 A))).fv)
      0

theorem nb093_fresh_086 (r : Var) :
    (nb093AlphaDummy091 r) ∉
      (((Class.cv (nb093AlphaDummy082 r))).fv ∪ ((Class.cv (nb093AlphaDummy082 r))).fv) :=
  by
  simpa only [nb093AlphaDummy091] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy082 r))).fv ∪ ((Class.cv (nb093AlphaDummy082 r))).fv)
      0

theorem nb093_fresh_087 (r : Var) :
    (nb093AlphaDummy087 r) ∉
      (((Class.cv (nb093AlphaDummy082 r))).fv ∪ ((Class.cv (nb093AlphaDummy083 r))).fv) :=
  by
  simpa only [nb093AlphaDummy087] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy082 r))).fv ∪ ((Class.cv (nb093AlphaDummy083 r))).fv)
      0

theorem nb093_fresh_088 (r : Var) :
    (nb093AlphaDummy093 r) ∉
      (((Class.cv (nb093AlphaDummy083 r))).fv ∪ ((Class.cv (nb093AlphaDummy083 r))).fv) :=
  by
  simpa only [nb093AlphaDummy093] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy083 r))).fv ∪ ((Class.cv (nb093AlphaDummy083 r))).fv)
      0

theorem nb093_fresh_089 (A : Class) :
    (nb093AlphaDummy108 A) ∉ (((Class.cv (nb093AlphaDummy101 A))).fv) := by
  simpa only [nb093AlphaDummy108] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy101 A))).fv) 0

theorem nb093_fresh_090 (A : Class) :
    (nb093AlphaDummy109 A) ∉ (((Class.cv (nb093AlphaDummy101 A))).fv) := by
  simpa only [nb093AlphaDummy109] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy101 A))).fv) 1

theorem nb093_distinct_091 (A : Class) :
    (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy109 A) := by
  simpa only [nb093AlphaDummy108, nb093AlphaDummy109] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy101 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb093_fresh_092 (r : Var) :
    (nb093AlphaDummy110 r) ∉ (((Class.cv (nb093AlphaDummy103 r))).fv) := by
  simpa only [nb093AlphaDummy110] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy103 r))).fv) 0

theorem nb093_fresh_093 (r : Var) :
    (nb093AlphaDummy111 r) ∉ (((Class.cv (nb093AlphaDummy103 r))).fv) := by
  simpa only [nb093AlphaDummy111] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy103 r))).fv) 1

theorem nb093_distinct_094 (r : Var) :
    (nb093AlphaDummy110 r) ≠ (nb093AlphaDummy111 r) := by
  simpa only [nb093AlphaDummy110, nb093AlphaDummy111] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy103 r))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb093_fresh_095 (A : Class) :
    (nb093AlphaDummy114 A) ∉
      (((Class.cv (nb093AlphaDummy108 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy114] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy108 A))).fv ∪ ((synC1c)).fv) 0

theorem nb093_fresh_096 (A : Class) :
    (nb093AlphaDummy115 A) ∉
      (((Class.cv (nb093AlphaDummy108 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy115] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy108 A))).fv ∪ ((synC1c)).fv) 1

theorem nb093_fresh_097 (A : Class) :
    (nb093AlphaDummy116 A) ∉
      (((Class.cv (nb093AlphaDummy108 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy116] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy108 A))).fv ∪ ((synC1c)).fv) 2

theorem nb093_distinct_098 (A : Class) :
    (nb093AlphaDummy114 A) ≠ (nb093AlphaDummy115 A) := by
  simpa only [nb093AlphaDummy114, nb093AlphaDummy115] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy108 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb093_distinct_099 (A : Class) :
    (nb093AlphaDummy114 A) ≠ (nb093AlphaDummy116 A) := by
  simpa only [nb093AlphaDummy114, nb093AlphaDummy116] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy108 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb093_distinct_100 (A : Class) :
    (nb093AlphaDummy115 A) ≠ (nb093AlphaDummy116 A) := by
  simpa only [nb093AlphaDummy115, nb093AlphaDummy116] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy108 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb093_fresh_101 (r : Var) :
    (nb093AlphaDummy117 r) ∉
      (((Class.cv (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy117] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) 0

theorem nb093_fresh_102 (r : Var) :
    (nb093AlphaDummy118 r) ∉
      (((Class.cv (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy118] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) 1

theorem nb093_fresh_103 (r : Var) :
    (nb093AlphaDummy119 r) ∉
      (((Class.cv (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy119] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) 2

theorem nb093_distinct_104 (r : Var) :
    (nb093AlphaDummy117 r) ≠ (nb093AlphaDummy118 r) := by
  simpa only [nb093AlphaDummy117, nb093AlphaDummy118] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb093_distinct_105 (r : Var) :
    (nb093AlphaDummy117 r) ≠ (nb093AlphaDummy119 r) := by
  simpa only [nb093AlphaDummy117, nb093AlphaDummy119] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb093_distinct_106 (r : Var) :
    (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy119 r) := by
  simpa only [nb093AlphaDummy118, nb093AlphaDummy119] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb093_fresh_107 (A : Class) :
    (nb093AlphaDummy126 A) ∉
      (((Class.cv (nb093AlphaDummy115 A))).fv ∪ ((Class.cv (nb093AlphaDummy115 A))).fv) :=
  by
  simpa only [nb093AlphaDummy126] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy115 A))).fv ∪ ((Class.cv (nb093AlphaDummy115 A))).fv)
      0

theorem nb093_fresh_108 (A : Class) :
    (nb093AlphaDummy122 A) ∉
      (((Class.cv (nb093AlphaDummy115 A))).fv ∪ ((Class.cv (nb093AlphaDummy116 A))).fv) :=
  by
  simpa only [nb093AlphaDummy122] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy115 A))).fv ∪ ((Class.cv (nb093AlphaDummy116 A))).fv)
      0

theorem nb093_fresh_109 (A : Class) :
    (nb093AlphaDummy128 A) ∉
      (((Class.cv (nb093AlphaDummy116 A))).fv ∪ ((Class.cv (nb093AlphaDummy116 A))).fv) :=
  by
  simpa only [nb093AlphaDummy128] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy116 A))).fv ∪ ((Class.cv (nb093AlphaDummy116 A))).fv)
      0

theorem nb093_fresh_110 (r : Var) :
    (nb093AlphaDummy127 r) ∉
      (((Class.cv (nb093AlphaDummy118 r))).fv ∪ ((Class.cv (nb093AlphaDummy118 r))).fv) :=
  by
  simpa only [nb093AlphaDummy127] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy118 r))).fv ∪ ((Class.cv (nb093AlphaDummy118 r))).fv)
      0

theorem nb093_fresh_111 (r : Var) :
    (nb093AlphaDummy123 r) ∉
      (((Class.cv (nb093AlphaDummy118 r))).fv ∪ ((Class.cv (nb093AlphaDummy119 r))).fv) :=
  by
  simpa only [nb093AlphaDummy123] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy118 r))).fv ∪ ((Class.cv (nb093AlphaDummy119 r))).fv)
      0

theorem nb093_fresh_112 (r : Var) :
    (nb093AlphaDummy129 r) ∉
      (((Class.cv (nb093AlphaDummy119 r))).fv ∪ ((Class.cv (nb093AlphaDummy119 r))).fv) :=
  by
  simpa only [nb093AlphaDummy129] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy119 r))).fv ∪ ((Class.cv (nb093AlphaDummy119 r))).fv)
      0

theorem nb093_fresh_113 (A : Class) :
    (nb093AlphaDummy142 A) ∉
      (((Class.cv (nb093AlphaDummy136 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy142] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy136 A))).fv ∪ ((synC1c)).fv) 0

theorem nb093_fresh_114 (A : Class) :
    (nb093AlphaDummy143 A) ∉
      (((Class.cv (nb093AlphaDummy136 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy143] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy136 A))).fv ∪ ((synC1c)).fv) 1

theorem nb093_fresh_115 (A : Class) :
    (nb093AlphaDummy144 A) ∉
      (((Class.cv (nb093AlphaDummy136 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy144] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy136 A))).fv ∪ ((synC1c)).fv) 2

theorem nb093_distinct_116 (A : Class) :
    (nb093AlphaDummy142 A) ≠ (nb093AlphaDummy143 A) := by
  simpa only [nb093AlphaDummy142, nb093AlphaDummy143] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy136 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb093_distinct_117 (A : Class) :
    (nb093AlphaDummy142 A) ≠ (nb093AlphaDummy144 A) := by
  simpa only [nb093AlphaDummy142, nb093AlphaDummy144] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy136 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb093_distinct_118 (A : Class) :
    (nb093AlphaDummy143 A) ≠ (nb093AlphaDummy144 A) := by
  simpa only [nb093AlphaDummy143, nb093AlphaDummy144] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy136 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb093_fresh_119 (r : Var) (d : Var) :
    (nb093AlphaDummy145 r d) ∉
      (((Class.cv (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy145] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv) 0

theorem nb093_fresh_120 (r : Var) (d : Var) :
    (nb093AlphaDummy146 r d) ∉
      (((Class.cv (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy146] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv) 1

theorem nb093_fresh_121 (r : Var) (d : Var) :
    (nb093AlphaDummy147 r d) ∉
      (((Class.cv (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb093AlphaDummy147] using
    freshVar_not_mem (((Class.cv (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv) 2

theorem nb093_distinct_122 (r : Var) (d : Var) :
    (nb093AlphaDummy145 r d) ≠ (nb093AlphaDummy146 r d) := by
  simpa only [nb093AlphaDummy145, nb093AlphaDummy146] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb093_distinct_123 (r : Var) (d : Var) :
    (nb093AlphaDummy145 r d) ≠ (nb093AlphaDummy147 r d) := by
  simpa only [nb093AlphaDummy145, nb093AlphaDummy147] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb093_distinct_124 (r : Var) (d : Var) :
    (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy147 r d) := by
  simpa only [nb093AlphaDummy146, nb093AlphaDummy147] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb093_fresh_125 (A : Class) :
    (nb093AlphaDummy154 A) ∉
      (((Class.cv (nb093AlphaDummy143 A))).fv ∪ ((Class.cv (nb093AlphaDummy143 A))).fv) :=
  by
  simpa only [nb093AlphaDummy154] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy143 A))).fv ∪ ((Class.cv (nb093AlphaDummy143 A))).fv)
      0

theorem nb093_fresh_126 (A : Class) :
    (nb093AlphaDummy150 A) ∉
      (((Class.cv (nb093AlphaDummy143 A))).fv ∪ ((Class.cv (nb093AlphaDummy144 A))).fv) :=
  by
  simpa only [nb093AlphaDummy150] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy143 A))).fv ∪ ((Class.cv (nb093AlphaDummy144 A))).fv)
      0

theorem nb093_fresh_127 (A : Class) :
    (nb093AlphaDummy156 A) ∉
      (((Class.cv (nb093AlphaDummy144 A))).fv ∪ ((Class.cv (nb093AlphaDummy144 A))).fv) :=
  by
  simpa only [nb093AlphaDummy156] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy144 A))).fv ∪ ((Class.cv (nb093AlphaDummy144 A))).fv)
      0

theorem nb093_fresh_128 (r : Var) (d : Var) :
    (nb093AlphaDummy155 r d) ∉
      (((Class.cv (nb093AlphaDummy146 r d))).fv ∪
        ((Class.cv (nb093AlphaDummy146 r d))).fv) :=
  by
  simpa only [nb093AlphaDummy155] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy146 r d))).fv ∪
        ((Class.cv (nb093AlphaDummy146 r d))).fv)
      0

theorem nb093_fresh_129 (r : Var) (d : Var) :
    (nb093AlphaDummy151 r d) ∉
      (((Class.cv (nb093AlphaDummy146 r d))).fv ∪
        ((Class.cv (nb093AlphaDummy147 r d))).fv) :=
  by
  simpa only [nb093AlphaDummy151] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy146 r d))).fv ∪
        ((Class.cv (nb093AlphaDummy147 r d))).fv)
      0

theorem nb093_fresh_130 (r : Var) (d : Var) :
    (nb093AlphaDummy157 r d) ∉
      (((Class.cv (nb093AlphaDummy147 r d))).fv ∪
        ((Class.cv (nb093AlphaDummy147 r d))).fv) :=
  by
  simpa only [nb093AlphaDummy157] using
    freshVar_not_mem
      (((Class.cv (nb093AlphaDummy147 r d))).fv ∪
        ((Class.cv (nb093AlphaDummy147 r d))).fv)
      0

theorem nb093_fresh_131 (r : Var) : (nb093AlphaDummy060 r) ∉ (((Class.cv r)).fv) := by
  simpa only [nb093AlphaDummy060] using freshVar_not_mem (((Class.cv r)).fv) 0

theorem nb093_fresh_132 (r : Var) : (nb093AlphaDummy061 r) ∉ (((Class.cv r)).fv) := by
  simpa only [nb093AlphaDummy061] using freshVar_not_mem (((Class.cv r)).fv) 1

theorem nb093_distinct_133 (r : Var) :
    (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy061 r) := by
  simpa only [nb093AlphaDummy060, nb093AlphaDummy061] using
    (freshVar_injective (((Class.cv r)).fv) (i := 0) (j := 1) (by decide))

theorem nb093_fresh_134 (r : Var) (d : Var) :
    (nb093AlphaDummy010 r d) ∉ (((Class.cv r)).fv ∪ ((Class.cv d)).fv) := by
  simpa only [nb093AlphaDummy010] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv d)).fv) 0

theorem nb093_fresh_135 (r : Var) (d : Var) :
    (nb093AlphaDummy011 r d) ∉ (((Class.cv r)).fv ∪ ((Class.cv d)).fv) := by
  simpa only [nb093AlphaDummy011] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv d)).fv) 1

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


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

theorem nb093_distinct_136 (r : Var) (d : Var) :
    (nb093AlphaDummy010 r d) ≠ (nb093AlphaDummy011 r d) := by
  simpa only [nb093AlphaDummy010, nb093AlphaDummy011] using
    (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv d)).fv) (i := 0) (j := 1) (by decide))

theorem nb093_fresh_137 (r : Var) :
    (nb093AlphaDummy055 r) ∉
      (((Class.cv r)).fv ∪ ((synCcompl (synCcnv (Class.cv r)))).fv) :=
  by
  simpa only [nb093AlphaDummy055] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((synCcompl (synCcnv (Class.cv r)))).fv) 0

theorem nb093_fresh_138 (A : Class) :
    (nb093AlphaDummy020 A) ∉
      (((Wff.classMem (Class.cv (nb093AlphaDummy016 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy016 A)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy016 A))).fv) :=
  by
  simpa only [nb093AlphaDummy020] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb093AlphaDummy016 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy016 A)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy016 A))).fv)
      0

theorem nb093_fresh_139 (r : Var) (d : Var) :
    (nb093AlphaDummy021 r d) ∉
      (((Wff.classMem (Class.cv (nb093AlphaDummy018 r d)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy018 r d)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy018 r d))).fv) :=
  by
  simpa only [nb093AlphaDummy021] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb093AlphaDummy018 r d)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy018 r d)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy018 r d))).fv)
      0

theorem nb093_fresh_140 (A : Class) :
    (nb093AlphaDummy076 A) ∉
      (((Wff.classMem (Class.cv (nb093AlphaDummy072 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy072 A)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy072 A))).fv) :=
  by
  simpa only [nb093AlphaDummy076] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb093AlphaDummy072 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy072 A)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy072 A))).fv)
      0

theorem nb093_fresh_141 (r : Var) :
    (nb093AlphaDummy077 r) ∉
      (((Wff.classMem (Class.cv (nb093AlphaDummy074 r)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy074 r)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy074 r))).fv) :=
  by
  simpa only [nb093AlphaDummy077] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb093AlphaDummy074 r)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy074 r)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy074 r))).fv)
      0

theorem nb093_fresh_142 (A : Class) :
    (nb093AlphaDummy112 A) ∉
      (((Wff.classMem (Class.cv (nb093AlphaDummy108 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy108 A)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy108 A))).fv) :=
  by
  simpa only [nb093AlphaDummy112] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb093AlphaDummy108 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy108 A)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy108 A))).fv)
      0

theorem nb093_fresh_143 (r : Var) :
    (nb093AlphaDummy113 r) ∉
      (((Wff.classMem (Class.cv (nb093AlphaDummy110 r)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy110 r)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy110 r))).fv) :=
  by
  simpa only [nb093AlphaDummy113] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb093AlphaDummy110 r)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy110 r)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy110 r))).fv)
      0

theorem nb093_fresh_144 (A : Class) :
    (nb093AlphaDummy140 A) ∉
      (((Wff.classMem (Class.cv (nb093AlphaDummy136 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy136 A)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy136 A))).fv) :=
  by
  simpa only [nb093AlphaDummy140] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb093AlphaDummy136 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy136 A)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy136 A))).fv)
      0

theorem nb093_fresh_145 (r : Var) (d : Var) :
    (nb093AlphaDummy141 r d) ∉
      (((Wff.classMem (Class.cv (nb093AlphaDummy138 r d)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy138 r d)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy138 r d))).fv) :=
  by
  simpa only [nb093AlphaDummy141] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb093AlphaDummy138 r d)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy138 r d)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy138 r d))).fv)
      0

theorem nb093_fresh_146 (A : Class) :
    (nb093AlphaDummy056 A) ∉
      (((synCcnv (Class.cv (nb093AlphaDummy001 A)))).fv ∪
        ((synCcnv (Class.cv (nb093AlphaDummy001 A)))).fv) :=
  by
  simpa only [nb093AlphaDummy056] using
    freshVar_not_mem
      (((synCcnv (Class.cv (nb093AlphaDummy001 A)))).fv ∪
        ((synCcnv (Class.cv (nb093AlphaDummy001 A)))).fv)
      0

theorem nb093_fresh_147 (r : Var) :
    (nb093AlphaDummy057 r) ∉
      (((synCcnv (Class.cv r))).fv ∪ ((synCcnv (Class.cv r))).fv) :=
  by
  simpa only [nb093AlphaDummy057] using
    freshVar_not_mem (((synCcnv (Class.cv r))).fv ∪ ((synCcnv (Class.cv r))).fv) 0

theorem nb093_fresh_148 (A : Class) :
    (nb093AlphaDummy012 A) ∉
      (((synCcompl (Class.cab (nb093AlphaDummy008 A)
              (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                  (synCphi (Class.cv (nb093AlphaDummy009 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy008 A)
              (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy000 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy009 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb093AlphaDummy012] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb093AlphaDummy008 A)
              (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                  (synCphi (Class.cv (nb093AlphaDummy009 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy008 A)
              (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy000 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy009 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb093_fresh_149 (r : Var) (d : Var) :
    (nb093AlphaDummy013 r d) ∉
      (((synCcompl (Class.cab (nb093AlphaDummy010 r d)
              (synWrex (nb093AlphaDummy011 r d) (Class.cv r)
                (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                  (synCphi (Class.cv (nb093AlphaDummy011 r d)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy010 r d)
              (synWrex (nb093AlphaDummy011 r d) (Class.cv d)
                (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy011 r d)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb093AlphaDummy013] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb093AlphaDummy010 r d)
              (synWrex (nb093AlphaDummy011 r d) (Class.cv r)
                (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                  (synCphi (Class.cv (nb093AlphaDummy011 r d)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy010 r d)
              (synWrex (nb093AlphaDummy011 r d) (Class.cv d)
                (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy011 r d)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb093_fresh_150 (A : Class) :
    (nb093AlphaDummy048 A) ∉
      (((synCcompl (Class.cab (nb093AlphaDummy044 A) (synWrex (nb093AlphaDummy045 A)
                (synCdif (Class.cv (nb093AlphaDummy001 A))
                  (synCcnv (Class.cv (nb093AlphaDummy001 A))))
                (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                  (synCphi (Class.cv (nb093AlphaDummy045 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy044 A)
              (synWrex (nb093AlphaDummy045 A) (Class.cv (nb093AlphaDummy000 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy045 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb093AlphaDummy048] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb093AlphaDummy044 A) (synWrex (nb093AlphaDummy045 A)
                (synCdif (Class.cv (nb093AlphaDummy001 A))
                  (synCcnv (Class.cv (nb093AlphaDummy001 A))))
                (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                  (synCphi (Class.cv (nb093AlphaDummy045 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy044 A)
              (synWrex (nb093AlphaDummy045 A) (Class.cv (nb093AlphaDummy000 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy045 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb093_fresh_151 (r : Var) (d : Var) :
    (nb093AlphaDummy049 r d) ∉
      (((synCcompl (Class.cab (nb093AlphaDummy046 r d) (synWrex (nb093AlphaDummy047 r d)
                (synCdif (Class.cv r) (synCcnv (Class.cv r)))
                (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                  (synCphi (Class.cv (nb093AlphaDummy047 r d)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy046 r d)
              (synWrex (nb093AlphaDummy047 r d) (Class.cv d)
                (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy047 r d)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb093AlphaDummy049] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb093AlphaDummy046 r d) (synWrex (nb093AlphaDummy047 r d)
                (synCdif (Class.cv r) (synCcnv (Class.cv r)))
                (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                  (synCphi (Class.cv (nb093AlphaDummy047 r d)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy046 r d)
              (synWrex (nb093AlphaDummy047 r d) (Class.cv d)
                (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy047 r d)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb093_fresh_152 (A : Class) :
    (nb093AlphaDummy068 A) ∉
      (((synCcompl (Class.cab (nb093AlphaDummy064 A)
              (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy058 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                  (synCphi (Class.cv (nb093AlphaDummy065 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy064 A)
              (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy059 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy065 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb093AlphaDummy068] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb093AlphaDummy064 A)
              (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy058 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                  (synCphi (Class.cv (nb093AlphaDummy065 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy064 A)
              (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy059 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy065 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb093_fresh_153 (r : Var) :
    (nb093AlphaDummy069 r) ∉
      (((synCcompl (Class.cab (nb093AlphaDummy066 r)
              (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy060 r))
                (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                  (synCphi (Class.cv (nb093AlphaDummy067 r)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy066 r)
              (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy061 r))
                (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy067 r)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb093AlphaDummy069] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb093AlphaDummy066 r)
              (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy060 r))
                (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                  (synCphi (Class.cv (nb093AlphaDummy067 r)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy066 r)
              (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy061 r))
                (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy067 r)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb093_fresh_154 (A : Class) :
    (nb093AlphaDummy104 A) ∉
      (((synCcompl (Class.cab (nb093AlphaDummy100 A)
              (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy059 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                  (synCphi (Class.cv (nb093AlphaDummy101 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy100 A)
              (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy058 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy101 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb093AlphaDummy104] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb093AlphaDummy100 A)
              (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy059 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                  (synCphi (Class.cv (nb093AlphaDummy101 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy100 A)
              (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy058 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy101 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb093_fresh_155 (r : Var) :
    (nb093AlphaDummy105 r) ∉
      (((synCcompl (Class.cab (nb093AlphaDummy102 r)
              (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy061 r))
                (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                  (synCphi (Class.cv (nb093AlphaDummy103 r)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy102 r)
              (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy060 r))
                (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy103 r)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb093AlphaDummy105] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb093AlphaDummy102 r)
              (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy061 r))
                (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                  (synCphi (Class.cv (nb093AlphaDummy103 r)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy102 r)
              (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy060 r))
                (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy103 r)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb093_fresh_156 (A : Class) :
    (nb093AlphaDummy032 A) ∉
      (((synCcompl (Class.cv (nb093AlphaDummy023 A)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy024 A)))).fv) :=
  by
  simpa only [nb093AlphaDummy032] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb093AlphaDummy023 A)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy024 A)))).fv)
      0

theorem nb093_fresh_157 (r : Var) (d : Var) :
    (nb093AlphaDummy033 r d) ∉
      (((synCcompl (Class.cv (nb093AlphaDummy026 r d)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy027 r d)))).fv) :=
  by
  simpa only [nb093AlphaDummy033] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb093AlphaDummy026 r d)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy027 r d)))).fv)
      0

theorem nb093_fresh_158 (A : Class) :
    (nb093AlphaDummy088 A) ∉
      (((synCcompl (Class.cv (nb093AlphaDummy079 A)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy080 A)))).fv) :=
  by
  simpa only [nb093AlphaDummy088] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb093AlphaDummy079 A)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy080 A)))).fv)
      0

theorem nb093_fresh_159 (r : Var) :
    (nb093AlphaDummy089 r) ∉
      (((synCcompl (Class.cv (nb093AlphaDummy082 r)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy083 r)))).fv) :=
  by
  simpa only [nb093AlphaDummy089] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb093AlphaDummy082 r)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy083 r)))).fv)
      0

theorem nb093_fresh_160 (A : Class) :
    (nb093AlphaDummy124 A) ∉
      (((synCcompl (Class.cv (nb093AlphaDummy115 A)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy116 A)))).fv) :=
  by
  simpa only [nb093AlphaDummy124] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb093AlphaDummy115 A)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy116 A)))).fv)
      0

theorem nb093_fresh_161 (r : Var) :
    (nb093AlphaDummy125 r) ∉
      (((synCcompl (Class.cv (nb093AlphaDummy118 r)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy119 r)))).fv) :=
  by
  simpa only [nb093AlphaDummy125] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb093AlphaDummy118 r)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy119 r)))).fv)
      0

theorem nb093_fresh_162 (A : Class) :
    (nb093AlphaDummy152 A) ∉
      (((synCcompl (Class.cv (nb093AlphaDummy143 A)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy144 A)))).fv) :=
  by
  simpa only [nb093AlphaDummy152] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb093AlphaDummy143 A)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy144 A)))).fv)
      0

theorem nb093_fresh_163 (r : Var) (d : Var) :
    (nb093AlphaDummy153 r d) ∉
      (((synCcompl (Class.cv (nb093AlphaDummy146 r d)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy147 r d)))).fv) :=
  by
  simpa only [nb093AlphaDummy153] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb093AlphaDummy146 r d)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy147 r d)))).fv)
      0

theorem nb093_fresh_164 (A : Class) :
    (nb093AlphaDummy040 A) ∉
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy009 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb093AlphaDummy040] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy009 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb093_fresh_165 (r : Var) (d : Var) :
    (nb093AlphaDummy041 r d) ∉
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy011 r d))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb093AlphaDummy041] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy011 r d))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb093_fresh_166 (A : Class) :
    (nb093AlphaDummy160 A) ∉
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy045 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb093AlphaDummy160] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy045 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb093_fresh_167 (r : Var) (d : Var) :
    (nb093AlphaDummy161 r d) ∉
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy047 r d))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb093AlphaDummy161] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy047 r d))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb093_fresh_168 (A : Class) :
    (nb093AlphaDummy096 A) ∉
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy065 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb093AlphaDummy096] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy065 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb093_fresh_169 (r : Var) :
    (nb093AlphaDummy097 r) ∉
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy067 r))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb093AlphaDummy097] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy067 r))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb093_fresh_170 (A : Class) :
    (nb093AlphaDummy132 A) ∉
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy101 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb093AlphaDummy132] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy101 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb093_fresh_171 (r : Var) :
    (nb093AlphaDummy133 r) ∉
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy103 r))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb093AlphaDummy133] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy103 r))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb093_fresh_172 (A : Class) :
    (nb093AlphaDummy044 A) ∉
      (((synCdif (Class.cv (nb093AlphaDummy001 A))
            (synCcnv (Class.cv (nb093AlphaDummy001 A))))).fv ∪
        ((Class.cv (nb093AlphaDummy000 A))).fv) :=
  by
  simpa only [nb093AlphaDummy044] using
    freshVar_not_mem
      (((synCdif (Class.cv (nb093AlphaDummy001 A))
            (synCcnv (Class.cv (nb093AlphaDummy001 A))))).fv ∪
        ((Class.cv (nb093AlphaDummy000 A))).fv)
      0

theorem nb093_fresh_173 (A : Class) :
    (nb093AlphaDummy045 A) ∉
      (((synCdif (Class.cv (nb093AlphaDummy001 A))
            (synCcnv (Class.cv (nb093AlphaDummy001 A))))).fv ∪
        ((Class.cv (nb093AlphaDummy000 A))).fv) :=
  by
  simpa only [nb093AlphaDummy045] using
    freshVar_not_mem
      (((synCdif (Class.cv (nb093AlphaDummy001 A))
            (synCcnv (Class.cv (nb093AlphaDummy001 A))))).fv ∪
        ((Class.cv (nb093AlphaDummy000 A))).fv)
      1

theorem nb093_distinct_174 (A : Class) :
    (nb093AlphaDummy044 A) ≠ (nb093AlphaDummy045 A) := by
  simpa only [nb093AlphaDummy044, nb093AlphaDummy045] using
    (freshVar_injective (((synCdif (Class.cv (nb093AlphaDummy001 A))
            (synCcnv (Class.cv (nb093AlphaDummy001 A))))).fv ∪
        ((Class.cv (nb093AlphaDummy000 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb093_fresh_175 (r : Var) (d : Var) :
    (nb093AlphaDummy046 r d) ∉
      (((synCdif (Class.cv r) (synCcnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv) :=
  by
  simpa only [nb093AlphaDummy046] using
    freshVar_not_mem
      (((synCdif (Class.cv r) (synCcnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv) 0

theorem nb093_fresh_176 (r : Var) (d : Var) :
    (nb093AlphaDummy047 r d) ∉
      (((synCdif (Class.cv r) (synCcnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv) :=
  by
  simpa only [nb093AlphaDummy047] using
    freshVar_not_mem
      (((synCdif (Class.cv r) (synCcnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv) 1

theorem nb093_distinct_177 (r : Var) (d : Var) :
    (nb093AlphaDummy046 r d) ≠ (nb093AlphaDummy047 r d) := by
  simpa only [nb093AlphaDummy046, nb093AlphaDummy047] using
    (freshVar_injective
      (((synCdif (Class.cv r) (synCcnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb093_fresh_178 (A : Class) :
    (nb093AlphaDummy004 A) ∉
      (((synClntpc A)).fv ∪ ((synCopab (nb093AlphaDummy001 A) (nb093AlphaDummy000 A)
            (synWbr (synCdif (Class.cv (nb093AlphaDummy001 A))
                (synCcnv (Class.cv (nb093AlphaDummy001 A))))
              (synCfound) (Class.cv (nb093AlphaDummy000 A))))).fv) :=
  by
  simpa only [nb093AlphaDummy004] using
    freshVar_not_mem
      (((synClntpc A)).fv ∪ ((synCopab (nb093AlphaDummy001 A) (nb093AlphaDummy000 A)
            (synWbr (synCdif (Class.cv (nb093AlphaDummy001 A))
                (synCcnv (Class.cv (nb093AlphaDummy001 A))))
              (synCfound) (Class.cv (nb093AlphaDummy000 A))))).fv)
      0

theorem nb093_fresh_179 (A : Class) (r : Var) (d : Var) :
    (nb093AlphaDummy005 A r d) ∉
      (((synClntpc A)).fv ∪ ((synCopab r d
            (synWbr (synCdif (Class.cv r) (synCcnv (Class.cv r))) (synCfound)
              (Class.cv d)))).fv) :=
  by
  simpa only [nb093AlphaDummy005] using
    freshVar_not_mem
      (((synClntpc A)).fv ∪ ((synCopab r d
            (synWbr (synCdif (Class.cv r) (synCcnv (Class.cv r))) (synCfound)
              (Class.cv d)))).fv)
      0

theorem nb093_fresh_180 (A : Class) :
    (nb093AlphaDummy052 A) ∉
      (((synCnin (Class.cv (nb093AlphaDummy001 A))
            (synCcompl (synCcnv (Class.cv (nb093AlphaDummy001 A)))))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy001 A))
            (synCcompl (synCcnv (Class.cv (nb093AlphaDummy001 A)))))).fv) :=
  by
  simpa only [nb093AlphaDummy052] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb093AlphaDummy001 A))
            (synCcompl (synCcnv (Class.cv (nb093AlphaDummy001 A)))))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy001 A))
            (synCcompl (synCcnv (Class.cv (nb093AlphaDummy001 A)))))).fv)
      0

theorem nb093_fresh_181 (A : Class) :
    (nb093AlphaDummy028 A) ∉
      (((synCnin (Class.cv (nb093AlphaDummy023 A))
            (Class.cv (nb093AlphaDummy024 A)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy023 A))
            (Class.cv (nb093AlphaDummy024 A)))).fv) :=
  by
  simpa only [nb093AlphaDummy028] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb093AlphaDummy023 A))
            (Class.cv (nb093AlphaDummy024 A)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy023 A))
            (Class.cv (nb093AlphaDummy024 A)))).fv)
      0

theorem nb093_fresh_182 (r : Var) (d : Var) :
    (nb093AlphaDummy029 r d) ∉
      (((synCnin (Class.cv (nb093AlphaDummy026 r d))
            (Class.cv (nb093AlphaDummy027 r d)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy026 r d))
            (Class.cv (nb093AlphaDummy027 r d)))).fv) :=
  by
  simpa only [nb093AlphaDummy029] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb093AlphaDummy026 r d))
            (Class.cv (nb093AlphaDummy027 r d)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy026 r d))
            (Class.cv (nb093AlphaDummy027 r d)))).fv)
      0

theorem nb093_fresh_183 (A : Class) :
    (nb093AlphaDummy084 A) ∉
      (((synCnin (Class.cv (nb093AlphaDummy079 A))
            (Class.cv (nb093AlphaDummy080 A)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy079 A))
            (Class.cv (nb093AlphaDummy080 A)))).fv) :=
  by
  simpa only [nb093AlphaDummy084] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb093AlphaDummy079 A))
            (Class.cv (nb093AlphaDummy080 A)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy079 A))
            (Class.cv (nb093AlphaDummy080 A)))).fv)
      0

theorem nb093_fresh_184 (r : Var) :
    (nb093AlphaDummy085 r) ∉
      (((synCnin (Class.cv (nb093AlphaDummy082 r))
            (Class.cv (nb093AlphaDummy083 r)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy082 r))
            (Class.cv (nb093AlphaDummy083 r)))).fv) :=
  by
  simpa only [nb093AlphaDummy085] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb093AlphaDummy082 r))
            (Class.cv (nb093AlphaDummy083 r)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy082 r))
            (Class.cv (nb093AlphaDummy083 r)))).fv)
      0

theorem nb093_fresh_185 (A : Class) :
    (nb093AlphaDummy120 A) ∉
      (((synCnin (Class.cv (nb093AlphaDummy115 A))
            (Class.cv (nb093AlphaDummy116 A)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy115 A))
            (Class.cv (nb093AlphaDummy116 A)))).fv) :=
  by
  simpa only [nb093AlphaDummy120] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb093AlphaDummy115 A))
            (Class.cv (nb093AlphaDummy116 A)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy115 A))
            (Class.cv (nb093AlphaDummy116 A)))).fv)
      0

theorem nb093_fresh_186 (r : Var) :
    (nb093AlphaDummy121 r) ∉
      (((synCnin (Class.cv (nb093AlphaDummy118 r))
            (Class.cv (nb093AlphaDummy119 r)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy118 r))
            (Class.cv (nb093AlphaDummy119 r)))).fv) :=
  by
  simpa only [nb093AlphaDummy121] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb093AlphaDummy118 r))
            (Class.cv (nb093AlphaDummy119 r)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy118 r))
            (Class.cv (nb093AlphaDummy119 r)))).fv)
      0

theorem nb093_fresh_187 (A : Class) :
    (nb093AlphaDummy148 A) ∉
      (((synCnin (Class.cv (nb093AlphaDummy143 A))
            (Class.cv (nb093AlphaDummy144 A)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy143 A))
            (Class.cv (nb093AlphaDummy144 A)))).fv) :=
  by
  simpa only [nb093AlphaDummy148] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb093AlphaDummy143 A))
            (Class.cv (nb093AlphaDummy144 A)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy143 A))
            (Class.cv (nb093AlphaDummy144 A)))).fv)
      0

theorem nb093_fresh_188 (r : Var) (d : Var) :
    (nb093AlphaDummy149 r d) ∉
      (((synCnin (Class.cv (nb093AlphaDummy146 r d))
            (Class.cv (nb093AlphaDummy147 r d)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy146 r d))
            (Class.cv (nb093AlphaDummy147 r d)))).fv) :=
  by
  simpa only [nb093AlphaDummy149] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb093AlphaDummy146 r d))
            (Class.cv (nb093AlphaDummy147 r d)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy146 r d))
            (Class.cv (nb093AlphaDummy147 r d)))).fv)
      0

theorem nb093_fresh_189 (r : Var) :
    (nb093AlphaDummy053 r) ∉
      (((synCnin (Class.cv r) (synCcompl (synCcnv (Class.cv r))))).fv ∪
        ((synCnin (Class.cv r) (synCcompl (synCcnv (Class.cv r))))).fv) :=
  by
  simpa only [nb093AlphaDummy053] using
    freshVar_not_mem
      (((synCnin (Class.cv r) (synCcompl (synCcnv (Class.cv r))))).fv ∪
        ((synCnin (Class.cv r) (synCcompl (synCcnv (Class.cv r))))).fv)
      0

theorem nb093_fresh_190 (A : Class) :
    (nb093AlphaDummy002 A) ∉
      (((synCnin (synClntpc A) (synCopab (nb093AlphaDummy001 A) (nb093AlphaDummy000 A)
              (synWbr (synCdif (Class.cv (nb093AlphaDummy001 A))
                  (synCcnv (Class.cv (nb093AlphaDummy001 A))))
                (synCfound) (Class.cv (nb093AlphaDummy000 A)))))).fv ∪
        ((synCnin (synClntpc A) (synCopab (nb093AlphaDummy001 A) (nb093AlphaDummy000 A)
              (synWbr (synCdif (Class.cv (nb093AlphaDummy001 A))
                  (synCcnv (Class.cv (nb093AlphaDummy001 A))))
                (synCfound) (Class.cv (nb093AlphaDummy000 A)))))).fv) :=
  by
  simpa only [nb093AlphaDummy002] using
    freshVar_not_mem
      (((synCnin (synClntpc A) (synCopab (nb093AlphaDummy001 A) (nb093AlphaDummy000 A)
              (synWbr (synCdif (Class.cv (nb093AlphaDummy001 A))
                  (synCcnv (Class.cv (nb093AlphaDummy001 A))))
                (synCfound) (Class.cv (nb093AlphaDummy000 A)))))).fv ∪
        ((synCnin (synClntpc A) (synCopab (nb093AlphaDummy001 A) (nb093AlphaDummy000 A)
              (synWbr (synCdif (Class.cv (nb093AlphaDummy001 A))
                  (synCcnv (Class.cv (nb093AlphaDummy001 A))))
                (synCfound) (Class.cv (nb093AlphaDummy000 A)))))).fv)
      0

theorem nb093_fresh_191 (A : Class) (r : Var) (d : Var) :
    (nb093AlphaDummy003 A r d) ∉
      (((synCnin (synClntpc A) (synCopab r d
              (synWbr (synCdif (Class.cv r) (synCcnv (Class.cv r))) (synCfound)
                (Class.cv d))))).fv ∪ ((synCnin (synClntpc A) (synCopab r d
              (synWbr (synCdif (Class.cv r) (synCcnv (Class.cv r))) (synCfound)
                (Class.cv d))))).fv) :=
  by
  simpa only [nb093AlphaDummy003] using
    freshVar_not_mem
      (((synCnin (synClntpc A) (synCopab r d
              (synWbr (synCdif (Class.cv r) (synCcnv (Class.cv r))) (synCfound)
                (Class.cv d))))).fv ∪ ((synCnin (synClntpc A) (synCopab r d
              (synWbr (synCdif (Class.cv r) (synCcnv (Class.cv r))) (synCfound)
                (Class.cv d))))).fv)
      0

theorem nb093_fresh_192 (A : Class) :
    (nb093AlphaDummy042 A) ∉
      (((synCphi (Class.cv (nb093AlphaDummy009 A)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy009 A)))).fv) :=
  by
  simpa only [nb093AlphaDummy042] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb093AlphaDummy009 A)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy009 A)))).fv)
      0

theorem nb093_fresh_193 (r : Var) (d : Var) :
    (nb093AlphaDummy043 r d) ∉
      (((synCphi (Class.cv (nb093AlphaDummy011 r d)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy011 r d)))).fv) :=
  by
  simpa only [nb093AlphaDummy043] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb093AlphaDummy011 r d)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy011 r d)))).fv)
      0

theorem nb093_fresh_194 (A : Class) :
    (nb093AlphaDummy162 A) ∉
      (((synCphi (Class.cv (nb093AlphaDummy045 A)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy045 A)))).fv) :=
  by
  simpa only [nb093AlphaDummy162] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb093AlphaDummy045 A)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy045 A)))).fv)
      0

theorem nb093_fresh_195 (r : Var) (d : Var) :
    (nb093AlphaDummy163 r d) ∉
      (((synCphi (Class.cv (nb093AlphaDummy047 r d)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy047 r d)))).fv) :=
  by
  simpa only [nb093AlphaDummy163] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb093AlphaDummy047 r d)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy047 r d)))).fv)
      0

theorem nb093_fresh_196 (A : Class) :
    (nb093AlphaDummy098 A) ∉
      (((synCphi (Class.cv (nb093AlphaDummy065 A)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy065 A)))).fv) :=
  by
  simpa only [nb093AlphaDummy098] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb093AlphaDummy065 A)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy065 A)))).fv)
      0

theorem nb093_fresh_197 (r : Var) :
    (nb093AlphaDummy099 r) ∉
      (((synCphi (Class.cv (nb093AlphaDummy067 r)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy067 r)))).fv) :=
  by
  simpa only [nb093AlphaDummy099] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb093AlphaDummy067 r)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy067 r)))).fv)
      0

theorem nb093_fresh_198 (A : Class) :
    (nb093AlphaDummy134 A) ∉
      (((synCphi (Class.cv (nb093AlphaDummy101 A)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy101 A)))).fv) :=
  by
  simpa only [nb093AlphaDummy134] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb093AlphaDummy101 A)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy101 A)))).fv)
      0

theorem nb093_fresh_199 (r : Var) :
    (nb093AlphaDummy135 r) ∉
      (((synCphi (Class.cv (nb093AlphaDummy103 r)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy103 r)))).fv) :=
  by
  simpa only [nb093AlphaDummy135] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb093AlphaDummy103 r)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy103 r)))).fv)
      0

theorem nb093_fresh_200 (A : Class) : (nb093AlphaDummy000 A) ∉ ((A).fv) := by
  simpa only [nb093AlphaDummy000] using freshVar_not_mem ((A).fv) 0

theorem nb093_fresh_201 (A : Class) : (nb093AlphaDummy001 A) ∉ ((A).fv) := by
  simpa only [nb093AlphaDummy001] using freshVar_not_mem ((A).fv) 1

theorem nb093_distinct_202 (A : Class) :
    (nb093AlphaDummy000 A) ≠ (nb093AlphaDummy001 A) := by
  simpa only [nb093AlphaDummy000, nb093AlphaDummy001] using
    (freshVar_injective ((A).fv) (i := 0) (j := 1) (by decide))

theorem nb093_fresh_203 (A : Class) :
    (nb093AlphaDummy006 A) ∉
      (({(nb093AlphaDummy001 A)} : Finset Var) ∪ ({(nb093AlphaDummy000 A)} : Finset Var) ∪
        ((synWbr (synCdif (Class.cv (nb093AlphaDummy001 A))
              (synCcnv (Class.cv (nb093AlphaDummy001 A))))
            (synCfound) (Class.cv (nb093AlphaDummy000 A)))).fv) :=
  by
  simpa only [nb093AlphaDummy006] using
    freshVar_not_mem
      (({(nb093AlphaDummy001 A)} : Finset Var) ∪ ({(nb093AlphaDummy000 A)} : Finset Var) ∪
        ((synWbr (synCdif (Class.cv (nb093AlphaDummy001 A))
              (synCcnv (Class.cv (nb093AlphaDummy001 A))))
            (synCfound) (Class.cv (nb093AlphaDummy000 A)))).fv)
      0

theorem nb093_fresh_204 (A : Class) :
    (nb093AlphaDummy062 A) ∉
      (({(nb093AlphaDummy058 A)} : Finset Var) ∪ ({(nb093AlphaDummy059 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb093AlphaDummy059 A)) (Class.cv (nb093AlphaDummy001 A))
            (Class.cv (nb093AlphaDummy058 A)))).fv) :=
  by
  simpa only [nb093AlphaDummy062] using
    freshVar_not_mem
      (({(nb093AlphaDummy058 A)} : Finset Var) ∪ ({(nb093AlphaDummy059 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb093AlphaDummy059 A)) (Class.cv (nb093AlphaDummy001 A))
            (Class.cv (nb093AlphaDummy058 A)))).fv)
      0

theorem nb093_fresh_205 (r : Var) :
    (nb093AlphaDummy063 r) ∉
      (({(nb093AlphaDummy060 r)} : Finset Var) ∪ ({(nb093AlphaDummy061 r)} : Finset Var) ∪
        ((synWbr (Class.cv (nb093AlphaDummy061 r)) (Class.cv r)
            (Class.cv (nb093AlphaDummy060 r)))).fv) :=
  by
  simpa only [nb093AlphaDummy063] using
    freshVar_not_mem
      (({(nb093AlphaDummy060 r)} : Finset Var) ∪ ({(nb093AlphaDummy061 r)} : Finset Var) ∪
        ((synWbr (Class.cv (nb093AlphaDummy061 r)) (Class.cv r)
            (Class.cv (nb093AlphaDummy060 r)))).fv)
      0

theorem nb093_fresh_206 (r : Var) (d : Var) :
    (nb093AlphaDummy007 r d) ∉
      (({ r } : Finset Var) ∪ ({ d } : Finset Var) ∪
        ((synWbr (synCdif (Class.cv r) (synCcnv (Class.cv r))) (synCfound)
            (Class.cv d))).fv) :=
  by
  simpa only [nb093AlphaDummy007] using
    freshVar_not_mem
      (({ r } : Finset Var) ∪ ({ d } : Finset Var) ∪
        ((synWbr (synCdif (Class.cv r) (synCcnv (Class.cv r))) (synCfound)
            (Class.cv d))).fv)
      0

theorem nb093_support_mem_0000 (A : Class) :
    (nb093AlphaDummy001 A) ∈
      (({(nb093AlphaDummy001 A)} : Finset Var) ∪ ({(nb093AlphaDummy000 A)} : Finset Var) ∪
        ((synWbr (synCdif (Class.cv (nb093AlphaDummy001 A))
              (synCcnv (Class.cv (nb093AlphaDummy001 A))))
            (synCfound) (Class.cv (nb093AlphaDummy000 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0001 (r : Var) (d : Var) :
    r ∈
      (({ r } : Finset Var) ∪ ({ d } : Finset Var) ∪
        ((synWbr (synCdif (Class.cv r) (synCcnv (Class.cv r))) (synCfound)
            (Class.cv d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0002 (A : Class) :
    (nb093AlphaDummy000 A) ∈
      (({(nb093AlphaDummy001 A)} : Finset Var) ∪ ({(nb093AlphaDummy000 A)} : Finset Var) ∪
        ((synWbr (synCdif (Class.cv (nb093AlphaDummy001 A))
              (synCcnv (Class.cv (nb093AlphaDummy001 A))))
            (synCfound) (Class.cv (nb093AlphaDummy000 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0003 (r : Var) (d : Var) :
    d ∈
      (({ r } : Finset Var) ∪ ({ d } : Finset Var) ∪
        ((synWbr (synCdif (Class.cv r) (synCcnv (Class.cv r))) (synCfound)
            (Class.cv d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0004 (A : Class) :
    (nb093AlphaDummy001 A) ∈
      (((Class.cv (nb093AlphaDummy001 A))).fv ∪ ((Class.cv (nb093AlphaDummy000 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0005 (A : Class) :
    (nb093AlphaDummy001 A) ∈
      (((synCcompl (Class.cab (nb093AlphaDummy008 A)
              (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                  (synCphi (Class.cv (nb093AlphaDummy009 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy008 A)
              (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy000 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy009 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy008 A) from (by
          unfold nb093AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0004 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy009 A) from (by
            unfold nb093AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0004 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0006 (r : Var) (d : Var) :
    r ∈ (((Class.cv r)).fv ∪ ((Class.cv d)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0007 (r : Var) (d : Var) :
    r ∈
      (((synCcompl (Class.cab (nb093AlphaDummy010 r d)
              (synWrex (nb093AlphaDummy011 r d) (Class.cv r)
                (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                  (synCphi (Class.cv (nb093AlphaDummy011 r d)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy010 r d)
              (synWrex (nb093AlphaDummy011 r d) (Class.cv d)
                (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy011 r d)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show r ≠ (nb093AlphaDummy010 r d) from (by
          unfold nb093AlphaDummy010;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0006 r d) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show r ≠ (nb093AlphaDummy011 r d) from (by
            unfold nb093AlphaDummy011;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0006 r d) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0008 (A : Class) :
    (nb093AlphaDummy001 A) ∈
      (((Class.cab (nb093AlphaDummy008 A)
            (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                (synCphi (Class.cv (nb093AlphaDummy009 A))))))).fv ∪
        ((Class.cab (nb093AlphaDummy008 A)
            (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                (synCphi (Class.cv (nb093AlphaDummy009 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy008 A) from (by
          unfold nb093AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0004 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy009 A) from (by
            unfold nb093AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0004 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0009 (r : Var) (d : Var) :
    r ∈
      (((Class.cab (nb093AlphaDummy010 r d)
            (synWrex (nb093AlphaDummy011 r d) (Class.cv r)
              (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                (synCphi (Class.cv (nb093AlphaDummy011 r d))))))).fv ∪
        ((Class.cab (nb093AlphaDummy010 r d)
            (synWrex (nb093AlphaDummy011 r d) (Class.cv r)
              (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                (synCphi (Class.cv (nb093AlphaDummy011 r d))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show r ≠ (nb093AlphaDummy010 r d) from (by
          unfold nb093AlphaDummy010;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0006 r d) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show r ≠ (nb093AlphaDummy011 r d) from (by
            unfold nb093AlphaDummy011;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0006 r d) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0010 (A : Class) :
    (nb093AlphaDummy009 A) ∈ (((Class.cv (nb093AlphaDummy009 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0011 (r : Var) (d : Var) :
    (nb093AlphaDummy011 r d) ∈ (((Class.cv (nb093AlphaDummy011 r d))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0012 (A : Class) :
    (nb093AlphaDummy016 A) ∈
      (((Wff.classMem (Class.cv (nb093AlphaDummy016 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy016 A)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy016 A))).fv) :=
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

theorem nb093_support_mem_0013 (r : Var) (d : Var) :
    (nb093AlphaDummy018 r d) ∈
      (((Wff.classMem (Class.cv (nb093AlphaDummy018 r d)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy018 r d)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy018 r d))).fv) :=
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

theorem nb093_support_mem_0014 (A : Class) :
    (nb093AlphaDummy016 A) ∈
      (((Class.cv (nb093AlphaDummy016 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0015 (r : Var) (d : Var) :
    (nb093AlphaDummy018 r d) ∈
      (((Class.cv (nb093AlphaDummy018 r d))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0016 (A : Class) :
    (nb093AlphaDummy023 A) ∈
      (((synCnin (Class.cv (nb093AlphaDummy023 A))
            (Class.cv (nb093AlphaDummy024 A)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy023 A))
            (Class.cv (nb093AlphaDummy024 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0017 (r : Var) (d : Var) :
    (nb093AlphaDummy026 r d) ∈
      (((synCnin (Class.cv (nb093AlphaDummy026 r d))
            (Class.cv (nb093AlphaDummy027 r d)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy026 r d))
            (Class.cv (nb093AlphaDummy027 r d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0018 (A : Class) :
    (nb093AlphaDummy023 A) ∈
      (((Class.cv (nb093AlphaDummy023 A))).fv ∪ ((Class.cv (nb093AlphaDummy024 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0019 (r : Var) (d : Var) :
    (nb093AlphaDummy026 r d) ∈
      (((Class.cv (nb093AlphaDummy026 r d))).fv ∪
        ((Class.cv (nb093AlphaDummy027 r d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0020 (A : Class) :
    (nb093AlphaDummy024 A) ∈
      (((synCnin (Class.cv (nb093AlphaDummy023 A))
            (Class.cv (nb093AlphaDummy024 A)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy023 A))
            (Class.cv (nb093AlphaDummy024 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0021 (r : Var) (d : Var) :
    (nb093AlphaDummy027 r d) ∈
      (((synCnin (Class.cv (nb093AlphaDummy026 r d))
            (Class.cv (nb093AlphaDummy027 r d)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy026 r d))
            (Class.cv (nb093AlphaDummy027 r d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0022 (A : Class) :
    (nb093AlphaDummy024 A) ∈
      (((Class.cv (nb093AlphaDummy023 A))).fv ∪ ((Class.cv (nb093AlphaDummy024 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0023 (r : Var) (d : Var) :
    (nb093AlphaDummy027 r d) ∈
      (((Class.cv (nb093AlphaDummy026 r d))).fv ∪
        ((Class.cv (nb093AlphaDummy027 r d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0024 (A : Class) :
    (nb093AlphaDummy023 A) ∈
      (((synCcompl (Class.cv (nb093AlphaDummy023 A)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy024 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0025 (r : Var) (d : Var) :
    (nb093AlphaDummy026 r d) ∈
      (((synCcompl (Class.cv (nb093AlphaDummy026 r d)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy027 r d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0026 (A : Class) :
    (nb093AlphaDummy023 A) ∈
      (((Class.cv (nb093AlphaDummy023 A))).fv ∪ ((Class.cv (nb093AlphaDummy023 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0027 (r : Var) (d : Var) :
    (nb093AlphaDummy026 r d) ∈
      (((Class.cv (nb093AlphaDummy026 r d))).fv ∪
        ((Class.cv (nb093AlphaDummy026 r d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0028 (A : Class) :
    (nb093AlphaDummy024 A) ∈
      (((synCcompl (Class.cv (nb093AlphaDummy023 A)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy024 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0029 (r : Var) (d : Var) :
    (nb093AlphaDummy027 r d) ∈
      (((synCcompl (Class.cv (nb093AlphaDummy026 r d)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy027 r d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0030 (A : Class) :
    (nb093AlphaDummy024 A) ∈
      (((Class.cv (nb093AlphaDummy024 A))).fv ∪ ((Class.cv (nb093AlphaDummy024 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0031 (r : Var) (d : Var) :
    (nb093AlphaDummy027 r d) ∈
      (((Class.cv (nb093AlphaDummy027 r d))).fv ∪
        ((Class.cv (nb093AlphaDummy027 r d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0032 (A : Class) :
    (nb093AlphaDummy000 A) ∈
      (((Class.cv (nb093AlphaDummy001 A))).fv ∪ ((Class.cv (nb093AlphaDummy000 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0033 (A : Class) :
    (nb093AlphaDummy000 A) ∈
      (((synCcompl (Class.cab (nb093AlphaDummy008 A)
              (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                  (synCphi (Class.cv (nb093AlphaDummy009 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy008 A)
              (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy000 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy009 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy000 A) ≠ (nb093AlphaDummy008 A) from (by
          unfold nb093AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0032 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy000 A) ≠ (nb093AlphaDummy009 A) from (by
            unfold nb093AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0032 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0034 (r : Var) (d : Var) :
    d ∈ (((Class.cv r)).fv ∪ ((Class.cv d)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0035 (r : Var) (d : Var) :
    d ∈
      (((synCcompl (Class.cab (nb093AlphaDummy010 r d)
              (synWrex (nb093AlphaDummy011 r d) (Class.cv r)
                (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                  (synCphi (Class.cv (nb093AlphaDummy011 r d)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy010 r d)
              (synWrex (nb093AlphaDummy011 r d) (Class.cv d)
                (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy011 r d)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show d ≠ (nb093AlphaDummy010 r d) from (by
          unfold nb093AlphaDummy010;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0034 r d) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show d ≠ (nb093AlphaDummy011 r d) from (by
            unfold nb093AlphaDummy011;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0034 r d) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0036 (A : Class) :
    (nb093AlphaDummy000 A) ∈
      (((Class.cab (nb093AlphaDummy008 A)
            (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy009 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy008 A)
            (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy009 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy000 A) ≠ (nb093AlphaDummy008 A) from (by
          unfold nb093AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0032 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy000 A) ≠ (nb093AlphaDummy009 A) from (by
            unfold nb093AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0032 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0037 (r : Var) (d : Var) :
    d ∈
      (((Class.cab (nb093AlphaDummy010 r d)
            (synWrex (nb093AlphaDummy011 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                (synCun (synCphi (Class.cv (nb093AlphaDummy011 r d)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy010 r d)
            (synWrex (nb093AlphaDummy011 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                (synCun (synCphi (Class.cv (nb093AlphaDummy011 r d)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show d ≠ (nb093AlphaDummy010 r d) from (by
          unfold nb093AlphaDummy010;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0034 r d) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show d ≠ (nb093AlphaDummy011 r d) from (by
            unfold nb093AlphaDummy011;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0034 r d) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0038 (A : Class) :
    (nb093AlphaDummy009 A) ∈
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy009 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0039 (r : Var) (d : Var) :
    (nb093AlphaDummy011 r d) ∈
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy011 r d))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0040 (A : Class) :
    (nb093AlphaDummy009 A) ∈
      (((synCphi (Class.cv (nb093AlphaDummy009 A)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy009 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0041 (r : Var) (d : Var) :
    (nb093AlphaDummy011 r d) ∈
      (((synCphi (Class.cv (nb093AlphaDummy011 r d)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy011 r d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0042 (A : Class) :
    (nb093AlphaDummy001 A) ∈
      (((synCdif (Class.cv (nb093AlphaDummy001 A))
            (synCcnv (Class.cv (nb093AlphaDummy001 A))))).fv ∪
        ((Class.cv (nb093AlphaDummy000 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cdif]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0043 (A : Class) :
    (nb093AlphaDummy001 A) ∈
      (((synCcompl (Class.cab (nb093AlphaDummy044 A) (synWrex (nb093AlphaDummy045 A)
                (synCdif (Class.cv (nb093AlphaDummy001 A))
                  (synCcnv (Class.cv (nb093AlphaDummy001 A))))
                (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                  (synCphi (Class.cv (nb093AlphaDummy045 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy044 A)
              (synWrex (nb093AlphaDummy045 A) (Class.cv (nb093AlphaDummy000 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy045 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy044 A) from (by
          unfold nb093AlphaDummy044;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0042 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy045 A) from (by
            unfold nb093AlphaDummy045;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0042 A) 1))))
    · rw [fv_syn_cdif]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0044 (r : Var) (d : Var) :
    r ∈ (((synCdif (Class.cv r) (synCcnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cdif]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0045 (r : Var) (d : Var) :
    r ∈
      (((synCcompl (Class.cab (nb093AlphaDummy046 r d) (synWrex (nb093AlphaDummy047 r d)
                (synCdif (Class.cv r) (synCcnv (Class.cv r)))
                (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                  (synCphi (Class.cv (nb093AlphaDummy047 r d)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy046 r d)
              (synWrex (nb093AlphaDummy047 r d) (Class.cv d)
                (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy047 r d)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show r ≠ (nb093AlphaDummy046 r d) from (by
          unfold nb093AlphaDummy046;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0044 r d) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show r ≠ (nb093AlphaDummy047 r d) from (by
            unfold nb093AlphaDummy047;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0044 r d) 1))))
    · rw [fv_syn_cdif]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0046 (A : Class) :
    (nb093AlphaDummy001 A) ∈
      (((Class.cab (nb093AlphaDummy044 A) (synWrex (nb093AlphaDummy045 A)
              (synCdif (Class.cv (nb093AlphaDummy001 A))
                (synCcnv (Class.cv (nb093AlphaDummy001 A))))
              (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                (synCphi (Class.cv (nb093AlphaDummy045 A))))))).fv ∪
        ((Class.cab (nb093AlphaDummy044 A) (synWrex (nb093AlphaDummy045 A)
              (synCdif (Class.cv (nb093AlphaDummy001 A))
                (synCcnv (Class.cv (nb093AlphaDummy001 A))))
              (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                (synCphi (Class.cv (nb093AlphaDummy045 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy044 A) from (by
          unfold nb093AlphaDummy044;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0042 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy045 A) from (by
            unfold nb093AlphaDummy045;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0042 A) 1))))
    · rw [fv_syn_cdif]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0047 (r : Var) (d : Var) :
    r ∈
      (((Class.cab (nb093AlphaDummy046 r d) (synWrex (nb093AlphaDummy047 r d)
              (synCdif (Class.cv r) (synCcnv (Class.cv r)))
              (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                (synCphi (Class.cv (nb093AlphaDummy047 r d))))))).fv ∪
        ((Class.cab (nb093AlphaDummy046 r d) (synWrex (nb093AlphaDummy047 r d)
              (synCdif (Class.cv r) (synCcnv (Class.cv r)))
              (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                (synCphi (Class.cv (nb093AlphaDummy047 r d))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show r ≠ (nb093AlphaDummy046 r d) from (by
          unfold nb093AlphaDummy046;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0044 r d) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show r ≠ (nb093AlphaDummy047 r d) from (by
            unfold nb093AlphaDummy047;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0044 r d) 1))))
    · rw [fv_syn_cdif]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0048 (A : Class) :
    (nb093AlphaDummy001 A) ∈
      (((synCnin (Class.cv (nb093AlphaDummy001 A))
            (synCcompl (synCcnv (Class.cv (nb093AlphaDummy001 A)))))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy001 A))
            (synCcompl (synCcnv (Class.cv (nb093AlphaDummy001 A)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0049 (r : Var) :
    r ∈
      (((synCnin (Class.cv r) (synCcompl (synCcnv (Class.cv r))))).fv ∪
        ((synCnin (Class.cv r) (synCcompl (synCcnv (Class.cv r))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0050 (A : Class) :
    (nb093AlphaDummy001 A) ∈
      (((Class.cv (nb093AlphaDummy001 A))).fv ∪
        ((synCcompl (synCcnv (Class.cv (nb093AlphaDummy001 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
