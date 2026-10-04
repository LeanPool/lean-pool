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

/-! Certificates from `NAPD051C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_000`. -/
@[expose]
noncomputable def nb051AlphaDummy000 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (({ x } : Finset Var) ∪ (A).fv ∪ ({ y } : Finset Var) ∪ (B).fv ∪ (C).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_001`. -/
@[expose]
noncomputable def nb051AlphaDummy001 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ({(nb051AlphaDummy000 x y A B C)} : Finset Var) ∪
      ((synWa (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
          (Wff.classEq (Class.cv (nb051AlphaDummy000 x y A B C)) C))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_002`. -/
@[expose]
noncomputable def nb051AlphaDummy002 (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
      ((synWa (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
          (Wff.classEq (Class.cv z) C))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_003`. -/
@[expose]
noncomputable def nb051AlphaDummy003 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((synCop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb051AlphaDummy000 x y A B C))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_004`. -/
@[expose]
noncomputable def nb051AlphaDummy004 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((synCop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb051AlphaDummy000 x y A B C))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_005`. -/
@[expose]
noncomputable def nb051AlphaDummy005 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_006`. -/
@[expose]
noncomputable def nb051AlphaDummy006 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_007`. -/
@[expose]
noncomputable def nb051AlphaDummy007 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb051AlphaDummy003 x y A B C)
            (synWrex (nb051AlphaDummy004 x y A B C) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))))))).fv ∪ ((synCcompl
          (Class.cab (nb051AlphaDummy003 x y A B C)
            (synWrex (nb051AlphaDummy004 x y A B C)
              (Class.cv (nb051AlphaDummy000 x y A B C))
              (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                (synCun (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_008`. -/
@[expose]
noncomputable def nb051AlphaDummy008 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb051AlphaDummy005 x y z)
            (synWrex (nb051AlphaDummy006 x y z) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                (synCphi (Class.cv (nb051AlphaDummy006 x y z)))))))).fv ∪ ((synCcompl
          (Class.cab (nb051AlphaDummy005 x y z)
            (synWrex (nb051AlphaDummy006 x y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                (synCun (synCphi (Class.cv (nb051AlphaDummy006 x y z)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_009`. -/
@[expose]
noncomputable def nb051AlphaDummy009 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Class.cab (nb051AlphaDummy003 x y A B C)
          (synWrex (nb051AlphaDummy004 x y A B C) (synCop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
              (synCphi (Class.cv (nb051AlphaDummy004 x y A B C))))))).fv ∪
      ((Class.cab (nb051AlphaDummy003 x y A B C)
          (synWrex (nb051AlphaDummy004 x y A B C) (synCop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
              (synCphi (Class.cv (nb051AlphaDummy004 x y A B C))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_010`. -/
@[expose]
noncomputable def nb051AlphaDummy010 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (nb051AlphaDummy005 x y z)
          (synWrex (nb051AlphaDummy006 x y z) (synCop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
              (synCphi (Class.cv (nb051AlphaDummy006 x y z))))))).fv ∪
      ((Class.cab (nb051AlphaDummy005 x y z)
          (synWrex (nb051AlphaDummy006 x y z) (synCop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
              (synCphi (Class.cv (nb051AlphaDummy006 x y z))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_011`. -/
@[expose]
noncomputable def nb051AlphaDummy011 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Class.cv (nb051AlphaDummy004 x y A B C))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_012`. -/
@[expose]
noncomputable def nb051AlphaDummy012 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Class.cv (nb051AlphaDummy004 x y A B C))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_013`. -/
@[expose]
noncomputable def nb051AlphaDummy013 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb051AlphaDummy006 x y z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_014`. -/
@[expose]
noncomputable def nb051AlphaDummy014 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb051AlphaDummy006 x y z))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_015`. -/
@[expose]
noncomputable def nb051AlphaDummy015 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb051AlphaDummy011 x y A B C)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb051AlphaDummy011 x y A B C)) (synC1c))).fv ∪
      ((Class.cv (nb051AlphaDummy011 x y A B C))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_016`. -/
@[expose]
noncomputable def nb051AlphaDummy016 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb051AlphaDummy013 x y z)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb051AlphaDummy013 x y z)) (synC1c))).fv ∪
      ((Class.cv (nb051AlphaDummy013 x y z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_017`. -/
@[expose]
noncomputable def nb051AlphaDummy017 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_018`. -/
@[expose]
noncomputable def nb051AlphaDummy018 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_019`. -/
@[expose]
noncomputable def nb051AlphaDummy019 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_020`. -/
@[expose]
noncomputable def nb051AlphaDummy020 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_021`. -/
@[expose]
noncomputable def nb051AlphaDummy021 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_022`. -/
@[expose]
noncomputable def nb051AlphaDummy022 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_023`. -/
@[expose]
noncomputable def nb051AlphaDummy023 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb051AlphaDummy018 x y A B C))
          (Class.cv (nb051AlphaDummy019 x y A B C)))).fv ∪
      ((synCnin (Class.cv (nb051AlphaDummy018 x y A B C))
          (Class.cv (nb051AlphaDummy019 x y A B C)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_024`. -/
@[expose]
noncomputable def nb051AlphaDummy024 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb051AlphaDummy021 x y z))
          (Class.cv (nb051AlphaDummy022 x y z)))).fv ∪
      ((synCnin (Class.cv (nb051AlphaDummy021 x y z))
          (Class.cv (nb051AlphaDummy022 x y z)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_025`. -/
@[expose]
noncomputable def nb051AlphaDummy025 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Class.cv (nb051AlphaDummy018 x y A B C))).fv ∪
      ((Class.cv (nb051AlphaDummy019 x y A B C))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_026`. -/
@[expose]
noncomputable def nb051AlphaDummy026 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb051AlphaDummy021 x y z))).fv ∪
      ((Class.cv (nb051AlphaDummy022 x y z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_027`. -/
@[expose]
noncomputable def nb051AlphaDummy027 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb051AlphaDummy018 x y A B C)))).fv ∪
      ((synCcompl (Class.cv (nb051AlphaDummy019 x y A B C)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_028`. -/
@[expose]
noncomputable def nb051AlphaDummy028 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb051AlphaDummy021 x y z)))).fv ∪
      ((synCcompl (Class.cv (nb051AlphaDummy022 x y z)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_029`. -/
@[expose]
noncomputable def nb051AlphaDummy029 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Class.cv (nb051AlphaDummy018 x y A B C))).fv ∪
      ((Class.cv (nb051AlphaDummy018 x y A B C))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_030`. -/
@[expose]
noncomputable def nb051AlphaDummy030 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb051AlphaDummy021 x y z))).fv ∪
      ((Class.cv (nb051AlphaDummy021 x y z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_031`. -/
@[expose]
noncomputable def nb051AlphaDummy031 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Class.cv (nb051AlphaDummy019 x y A B C))).fv ∪
      ((Class.cv (nb051AlphaDummy019 x y A B C))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_032`. -/
@[expose]
noncomputable def nb051AlphaDummy032 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb051AlphaDummy022 x y z))).fv ∪
      ((Class.cv (nb051AlphaDummy022 x y z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_033`. -/
@[expose]
noncomputable def nb051AlphaDummy033 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Class.cab (nb051AlphaDummy003 x y A B C)
          (synWrex (nb051AlphaDummy004 x y A B C)
            (Class.cv (nb051AlphaDummy000 x y A B C))
            (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
              (synCun (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb051AlphaDummy003 x y A B C)
          (synWrex (nb051AlphaDummy004 x y A B C)
            (Class.cv (nb051AlphaDummy000 x y A B C))
            (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
              (synCun (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_034`. -/
@[expose]
noncomputable def nb051AlphaDummy034 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (nb051AlphaDummy005 x y z)
          (synWrex (nb051AlphaDummy006 x y z) (Class.cv z)
            (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
              (synCun (synCphi (Class.cv (nb051AlphaDummy006 x y z)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb051AlphaDummy005 x y z)
          (synWrex (nb051AlphaDummy006 x y z) (Class.cv z)
            (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
              (synCun (synCphi (Class.cv (nb051AlphaDummy006 x y z)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_035`. -/
@[expose]
noncomputable def nb051AlphaDummy035 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb051AlphaDummy004 x y A B C))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_036`. -/
@[expose]
noncomputable def nb051AlphaDummy036 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb051AlphaDummy006 x y z))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_037`. -/
@[expose]
noncomputable def nb051AlphaDummy037 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))).fv ∪
      ((synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb051_alpha_dummy_038`. -/
@[expose]
noncomputable def nb051AlphaDummy038 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb051AlphaDummy006 x y z)))).fv ∪
      ((synCphi (Class.cv (nb051AlphaDummy006 x y z)))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part002`. -/


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

theorem nb051_fresh_000 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy033 x y A B C) ∉
      (((Class.cab (nb051AlphaDummy003 x y A B C) (synWrex (nb051AlphaDummy004 x y A B C)
              (Class.cv (nb051AlphaDummy000 x y A B C))
              (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                (synCun (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb051AlphaDummy003 x y A B C)
            (synWrex (nb051AlphaDummy004 x y A B C)
              (Class.cv (nb051AlphaDummy000 x y A B C))
              (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                (synCun (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb051AlphaDummy033] using
    freshVar_not_mem
      (((Class.cab (nb051AlphaDummy003 x y A B C) (synWrex (nb051AlphaDummy004 x y A B C)
              (Class.cv (nb051AlphaDummy000 x y A B C))
              (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                (synCun (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb051AlphaDummy003 x y A B C)
            (synWrex (nb051AlphaDummy004 x y A B C)
              (Class.cv (nb051AlphaDummy000 x y A B C))
              (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                (synCun (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb051_fresh_001 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy009 x y A B C) ∉
      (((Class.cab (nb051AlphaDummy003 x y A B C) (synWrex (nb051AlphaDummy004 x y A B C)
              (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                (synCphi (Class.cv (nb051AlphaDummy004 x y A B C))))))).fv ∪
        ((Class.cab (nb051AlphaDummy003 x y A B C)
            (synWrex (nb051AlphaDummy004 x y A B C) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                (synCphi (Class.cv (nb051AlphaDummy004 x y A B C))))))).fv) :=
  by
  simpa only [nb051AlphaDummy009] using
    freshVar_not_mem
      (((Class.cab (nb051AlphaDummy003 x y A B C) (synWrex (nb051AlphaDummy004 x y A B C)
              (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                (synCphi (Class.cv (nb051AlphaDummy004 x y A B C))))))).fv ∪
        ((Class.cab (nb051AlphaDummy003 x y A B C)
            (synWrex (nb051AlphaDummy004 x y A B C) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                (synCphi (Class.cv (nb051AlphaDummy004 x y A B C))))))).fv)
      0

theorem nb051_fresh_002 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy034 x y z) ∉
      (((Class.cab (nb051AlphaDummy005 x y z)
            (synWrex (nb051AlphaDummy006 x y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                (synCun (synCphi (Class.cv (nb051AlphaDummy006 x y z)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb051AlphaDummy005 x y z)
            (synWrex (nb051AlphaDummy006 x y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                (synCun (synCphi (Class.cv (nb051AlphaDummy006 x y z)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb051AlphaDummy034] using
    freshVar_not_mem
      (((Class.cab (nb051AlphaDummy005 x y z)
            (synWrex (nb051AlphaDummy006 x y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                (synCun (synCphi (Class.cv (nb051AlphaDummy006 x y z)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb051AlphaDummy005 x y z)
            (synWrex (nb051AlphaDummy006 x y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                (synCun (synCphi (Class.cv (nb051AlphaDummy006 x y z)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb051_fresh_003 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy010 x y z) ∉
      (((Class.cab (nb051AlphaDummy005 x y z)
            (synWrex (nb051AlphaDummy006 x y z) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                (synCphi (Class.cv (nb051AlphaDummy006 x y z))))))).fv ∪
        ((Class.cab (nb051AlphaDummy005 x y z)
            (synWrex (nb051AlphaDummy006 x y z) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                (synCphi (Class.cv (nb051AlphaDummy006 x y z))))))).fv) :=
  by
  simpa only [nb051AlphaDummy010] using
    freshVar_not_mem
      (((Class.cab (nb051AlphaDummy005 x y z)
            (synWrex (nb051AlphaDummy006 x y z) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                (synCphi (Class.cv (nb051AlphaDummy006 x y z))))))).fv ∪
        ((Class.cab (nb051AlphaDummy005 x y z)
            (synWrex (nb051AlphaDummy006 x y z) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                (synCphi (Class.cv (nb051AlphaDummy006 x y z))))))).fv)
      0

theorem nb051_fresh_004 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy011 x y A B C) ∉
      (((Class.cv (nb051AlphaDummy004 x y A B C))).fv) :=
  by
  simpa only [nb051AlphaDummy011] using
    freshVar_not_mem (((Class.cv (nb051AlphaDummy004 x y A B C))).fv) 0

theorem nb051_fresh_005 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy012 x y A B C) ∉
      (((Class.cv (nb051AlphaDummy004 x y A B C))).fv) :=
  by
  simpa only [nb051AlphaDummy012] using
    freshVar_not_mem (((Class.cv (nb051AlphaDummy004 x y A B C))).fv) 1

theorem nb051_distinct_006 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy011 x y A B C) ≠ (nb051AlphaDummy012 x y A B C) := by
  simpa only [nb051AlphaDummy011, nb051AlphaDummy012] using
    (freshVar_injective (((Class.cv (nb051AlphaDummy004 x y A B C))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb051_fresh_007 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy013 x y z) ∉ (((Class.cv (nb051AlphaDummy006 x y z))).fv) := by
  simpa only [nb051AlphaDummy013] using
    freshVar_not_mem (((Class.cv (nb051AlphaDummy006 x y z))).fv) 0

theorem nb051_fresh_008 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy014 x y z) ∉ (((Class.cv (nb051AlphaDummy006 x y z))).fv) := by
  simpa only [nb051AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb051AlphaDummy006 x y z))).fv) 1

theorem nb051_distinct_009 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy013 x y z) ≠ (nb051AlphaDummy014 x y z) := by
  simpa only [nb051AlphaDummy013, nb051AlphaDummy014] using
    (freshVar_injective (((Class.cv (nb051AlphaDummy006 x y z))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb051_fresh_010 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy017 x y A B C) ∉
      (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb051AlphaDummy017] using
    freshVar_not_mem (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪ ((synC1c)).fv)
      0

theorem nb051_fresh_011 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy018 x y A B C) ∉
      (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb051AlphaDummy018] using
    freshVar_not_mem (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪ ((synC1c)).fv)
      1

theorem nb051_fresh_012 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy019 x y A B C) ∉
      (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb051AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪ ((synC1c)).fv)
      2

theorem nb051_distinct_013 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy017 x y A B C) ≠ (nb051AlphaDummy018 x y A B C) := by
  simpa only [nb051AlphaDummy017, nb051AlphaDummy018] using
    (freshVar_injective
      (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪ ((synC1c)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb051_distinct_014 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy017 x y A B C) ≠ (nb051AlphaDummy019 x y A B C) := by
  simpa only [nb051AlphaDummy017, nb051AlphaDummy019] using
    (freshVar_injective
      (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪ ((synC1c)).fv) (i := 0) (j :=
      2) (by decide))

theorem nb051_distinct_015 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy018 x y A B C) ≠ (nb051AlphaDummy019 x y A B C) := by
  simpa only [nb051AlphaDummy018, nb051AlphaDummy019] using
    (freshVar_injective
      (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪ ((synC1c)).fv) (i := 1) (j :=
      2) (by decide))

theorem nb051_fresh_016 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy020 x y z) ∉
      (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb051AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv) 0

theorem nb051_fresh_017 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy021 x y z) ∉
      (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb051AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv) 1

theorem nb051_fresh_018 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy022 x y z) ∉
      (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb051AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv) 2

theorem nb051_distinct_019 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy020 x y z) ≠ (nb051AlphaDummy021 x y z) := by
  simpa only [nb051AlphaDummy020, nb051AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb051_distinct_020 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy020 x y z) ≠ (nb051AlphaDummy022 x y z) := by
  simpa only [nb051AlphaDummy020, nb051AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb051_distinct_021 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy021 x y z) ≠ (nb051AlphaDummy022 x y z) := by
  simpa only [nb051AlphaDummy021, nb051AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb051_fresh_022 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy029 x y A B C) ∉
      (((Class.cv (nb051AlphaDummy018 x y A B C))).fv ∪
        ((Class.cv (nb051AlphaDummy018 x y A B C))).fv) :=
  by
  simpa only [nb051AlphaDummy029] using
    freshVar_not_mem
      (((Class.cv (nb051AlphaDummy018 x y A B C))).fv ∪
        ((Class.cv (nb051AlphaDummy018 x y A B C))).fv)
      0

theorem nb051_fresh_023 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy025 x y A B C) ∉
      (((Class.cv (nb051AlphaDummy018 x y A B C))).fv ∪
        ((Class.cv (nb051AlphaDummy019 x y A B C))).fv) :=
  by
  simpa only [nb051AlphaDummy025] using
    freshVar_not_mem
      (((Class.cv (nb051AlphaDummy018 x y A B C))).fv ∪
        ((Class.cv (nb051AlphaDummy019 x y A B C))).fv)
      0

theorem nb051_fresh_024 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy031 x y A B C) ∉
      (((Class.cv (nb051AlphaDummy019 x y A B C))).fv ∪
        ((Class.cv (nb051AlphaDummy019 x y A B C))).fv) :=
  by
  simpa only [nb051AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb051AlphaDummy019 x y A B C))).fv ∪
        ((Class.cv (nb051AlphaDummy019 x y A B C))).fv)
      0

theorem nb051_fresh_025 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy030 x y z) ∉
      (((Class.cv (nb051AlphaDummy021 x y z))).fv ∪
        ((Class.cv (nb051AlphaDummy021 x y z))).fv) :=
  by
  simpa only [nb051AlphaDummy030] using
    freshVar_not_mem
      (((Class.cv (nb051AlphaDummy021 x y z))).fv ∪
        ((Class.cv (nb051AlphaDummy021 x y z))).fv)
      0

theorem nb051_fresh_026 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy026 x y z) ∉
      (((Class.cv (nb051AlphaDummy021 x y z))).fv ∪
        ((Class.cv (nb051AlphaDummy022 x y z))).fv) :=
  by
  simpa only [nb051AlphaDummy026] using
    freshVar_not_mem
      (((Class.cv (nb051AlphaDummy021 x y z))).fv ∪
        ((Class.cv (nb051AlphaDummy022 x y z))).fv)
      0

theorem nb051_fresh_027 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy032 x y z) ∉
      (((Class.cv (nb051AlphaDummy022 x y z))).fv ∪
        ((Class.cv (nb051AlphaDummy022 x y z))).fv) :=
  by
  simpa only [nb051AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb051AlphaDummy022 x y z))).fv ∪
        ((Class.cv (nb051AlphaDummy022 x y z))).fv)
      0

theorem nb051_fresh_028 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy015 x y A B C) ∉
      (((Wff.classMem (Class.cv (nb051AlphaDummy011 x y A B C)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb051AlphaDummy011 x y A B C)) (synC1c))).fv ∪
        ((Class.cv (nb051AlphaDummy011 x y A B C))).fv) :=
  by
  simpa only [nb051AlphaDummy015] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb051AlphaDummy011 x y A B C)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb051AlphaDummy011 x y A B C)) (synC1c))).fv ∪
        ((Class.cv (nb051AlphaDummy011 x y A B C))).fv)
      0

theorem nb051_fresh_029 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy016 x y z) ∉
      (((Wff.classMem (Class.cv (nb051AlphaDummy013 x y z)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb051AlphaDummy013 x y z)) (synC1c))).fv ∪
        ((Class.cv (nb051AlphaDummy013 x y z))).fv) :=
  by
  simpa only [nb051AlphaDummy016] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb051AlphaDummy013 x y z)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb051AlphaDummy013 x y z)) (synC1c))).fv ∪
        ((Class.cv (nb051AlphaDummy013 x y z))).fv)
      0

theorem nb051_fresh_030 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy007 x y A B C) ∉
      (((synCcompl (Class.cab (nb051AlphaDummy003 x y A B C)
              (synWrex (nb051AlphaDummy004 x y A B C) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                  (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))))))).fv ∪ ((synCcompl
            (Class.cab (nb051AlphaDummy003 x y A B C)
              (synWrex (nb051AlphaDummy004 x y A B C)
                (Class.cv (nb051AlphaDummy000 x y A B C))
                (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                  (synCun (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb051AlphaDummy007] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb051AlphaDummy003 x y A B C)
              (synWrex (nb051AlphaDummy004 x y A B C) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                  (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))))))).fv ∪ ((synCcompl
            (Class.cab (nb051AlphaDummy003 x y A B C)
              (synWrex (nb051AlphaDummy004 x y A B C)
                (Class.cv (nb051AlphaDummy000 x y A B C))
                (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                  (synCun (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb051_fresh_031 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy008 x y z) ∉
      (((synCcompl (Class.cab (nb051AlphaDummy005 x y z)
              (synWrex (nb051AlphaDummy006 x y z) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                  (synCphi (Class.cv (nb051AlphaDummy006 x y z)))))))).fv ∪ ((synCcompl
            (Class.cab (nb051AlphaDummy005 x y z)
              (synWrex (nb051AlphaDummy006 x y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                  (synCun (synCphi (Class.cv (nb051AlphaDummy006 x y z)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb051AlphaDummy008] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb051AlphaDummy005 x y z)
              (synWrex (nb051AlphaDummy006 x y z) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                  (synCphi (Class.cv (nb051AlphaDummy006 x y z)))))))).fv ∪ ((synCcompl
            (Class.cab (nb051AlphaDummy005 x y z)
              (synWrex (nb051AlphaDummy006 x y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                  (synCun (synCphi (Class.cv (nb051AlphaDummy006 x y z)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb051_fresh_032 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy027 x y A B C) ∉
      (((synCcompl (Class.cv (nb051AlphaDummy018 x y A B C)))).fv ∪
        ((synCcompl (Class.cv (nb051AlphaDummy019 x y A B C)))).fv) :=
  by
  simpa only [nb051AlphaDummy027] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb051AlphaDummy018 x y A B C)))).fv ∪
        ((synCcompl (Class.cv (nb051AlphaDummy019 x y A B C)))).fv)
      0

theorem nb051_fresh_033 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy028 x y z) ∉
      (((synCcompl (Class.cv (nb051AlphaDummy021 x y z)))).fv ∪
        ((synCcompl (Class.cv (nb051AlphaDummy022 x y z)))).fv) :=
  by
  simpa only [nb051AlphaDummy028] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb051AlphaDummy021 x y z)))).fv ∪
        ((synCcompl (Class.cv (nb051AlphaDummy022 x y z)))).fv)
      0

theorem nb051_fresh_034 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy035 x y A B C) ∉
      (((synCcompl (synCphi (Class.cv (nb051AlphaDummy004 x y A B C))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb051AlphaDummy035] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb051AlphaDummy004 x y A B C))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb051_fresh_035 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy036 x y z) ∉
      (((synCcompl (synCphi (Class.cv (nb051AlphaDummy006 x y z))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb051AlphaDummy036] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb051AlphaDummy006 x y z))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb051_fresh_036 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy023 x y A B C) ∉
      (((synCnin (Class.cv (nb051AlphaDummy018 x y A B C))
            (Class.cv (nb051AlphaDummy019 x y A B C)))).fv ∪
        ((synCnin (Class.cv (nb051AlphaDummy018 x y A B C))
            (Class.cv (nb051AlphaDummy019 x y A B C)))).fv) :=
  by
  simpa only [nb051AlphaDummy023] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb051AlphaDummy018 x y A B C))
            (Class.cv (nb051AlphaDummy019 x y A B C)))).fv ∪
        ((synCnin (Class.cv (nb051AlphaDummy018 x y A B C))
            (Class.cv (nb051AlphaDummy019 x y A B C)))).fv)
      0

theorem nb051_fresh_037 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy024 x y z) ∉
      (((synCnin (Class.cv (nb051AlphaDummy021 x y z))
            (Class.cv (nb051AlphaDummy022 x y z)))).fv ∪
        ((synCnin (Class.cv (nb051AlphaDummy021 x y z))
            (Class.cv (nb051AlphaDummy022 x y z)))).fv) :=
  by
  simpa only [nb051AlphaDummy024] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb051AlphaDummy021 x y z))
            (Class.cv (nb051AlphaDummy022 x y z)))).fv ∪
        ((synCnin (Class.cv (nb051AlphaDummy021 x y z))
            (Class.cv (nb051AlphaDummy022 x y z)))).fv)
      0

theorem nb051_fresh_038 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy003 x y A B C) ∉
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb051AlphaDummy000 x y A B C))).fv) :=
  by
  simpa only [nb051AlphaDummy003] using
    freshVar_not_mem
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb051AlphaDummy000 x y A B C))).fv)
      0

theorem nb051_fresh_039 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy004 x y A B C) ∉
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb051AlphaDummy000 x y A B C))).fv) :=
  by
  simpa only [nb051AlphaDummy004] using
    freshVar_not_mem
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb051AlphaDummy000 x y A B C))).fv)
      1

theorem nb051_distinct_040 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy003 x y A B C) ≠ (nb051AlphaDummy004 x y A B C) := by
  simpa only [nb051AlphaDummy003, nb051AlphaDummy004] using
    (freshVar_injective (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb051AlphaDummy000 x y A B C))).fv) (i := 0) (j := 1) (by decide))

theorem nb051_fresh_041 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy005 x y z) ∉
      (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) :=
  by
  simpa only [nb051AlphaDummy005] using
    freshVar_not_mem (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) 0

theorem nb051_fresh_042 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy006 x y z) ∉
      (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) :=
  by
  simpa only [nb051AlphaDummy006] using
    freshVar_not_mem (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) 1

theorem nb051_distinct_043 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy005 x y z) ≠ (nb051AlphaDummy006 x y z) := by
  simpa only [nb051AlphaDummy005, nb051AlphaDummy006] using
    (freshVar_injective (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb051_fresh_044 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy037 x y A B C) ∉
      (((synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))).fv ∪
        ((synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))).fv) :=
  by
  simpa only [nb051AlphaDummy037] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))).fv ∪
        ((synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))).fv)
      0

theorem nb051_fresh_045 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy038 x y z) ∉
      (((synCphi (Class.cv (nb051AlphaDummy006 x y z)))).fv ∪
        ((synCphi (Class.cv (nb051AlphaDummy006 x y z)))).fv) :=
  by
  simpa only [nb051AlphaDummy038] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb051AlphaDummy006 x y z)))).fv ∪
        ((synCphi (Class.cv (nb051AlphaDummy006 x y z)))).fv)
      0

theorem nb051_fresh_046 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy000 x y A B C) ∉
      (({ x } : Finset Var) ∪ (A).fv ∪ ({ y } : Finset Var) ∪ (B).fv ∪ (C).fv) :=
  by
  simpa only [nb051AlphaDummy000] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ (A).fv ∪ ({ y } : Finset Var) ∪ (B).fv ∪ (C).fv) 0

theorem nb051_fresh_047 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy001 x y A B C) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb051AlphaDummy000 x y A B C)} : Finset Var) ∪
        ((synWa (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
            (Wff.classEq (Class.cv (nb051AlphaDummy000 x y A B C)) C))).fv) :=
  by
  simpa only [nb051AlphaDummy001] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb051AlphaDummy000 x y A B C)} : Finset Var) ∪
        ((synWa (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
            (Wff.classEq (Class.cv (nb051AlphaDummy000 x y A B C)) C))).fv)
      0

theorem nb051_fresh_048 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) :
    (nb051AlphaDummy002 x y z A B C) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
        ((synWa (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
            (Wff.classEq (Class.cv z) C))).fv) :=
  by
  simpa only [nb051AlphaDummy002] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
        ((synWa (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
            (Wff.classEq (Class.cv z) C))).fv)
      0

theorem nb051_support_mem_0000 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb051AlphaDummy000 x y A B C)} : Finset Var) ∪
        ((synWa (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
            (Wff.classEq (Class.cv (nb051AlphaDummy000 x y A B C)) C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part003`. -/


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

theorem nb051_support_mem_0001 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
        ((synWa (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
            (Wff.classEq (Class.cv z) C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0002 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb051AlphaDummy000 x y A B C)} : Finset Var) ∪
        ((synWa (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
            (Wff.classEq (Class.cv (nb051AlphaDummy000 x y A B C)) C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0003 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
        ((synWa (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
            (Wff.classEq (Class.cv z) C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0004 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy000 x y A B C) ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb051AlphaDummy000 x y A B C)} : Finset Var) ∪
        ((synWa (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
            (Wff.classEq (Class.cv (nb051AlphaDummy000 x y A B C)) C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0005 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) :
    z ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
        ((synWa (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
            (Wff.classEq (Class.cv z) C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0006 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    x ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb051AlphaDummy000 x y A B C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0007 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    y ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb051AlphaDummy000 x y A B C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0008 (x : Var) (y : Var) (z : Var) :
    x ∈ (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0009 (x : Var) (y : Var) (z : Var) :
    y ∈ (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0010 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    x ∈
      (((Class.cab (nb051AlphaDummy003 x y A B C) (synWrex (nb051AlphaDummy004 x y A B C)
              (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                (synCphi (Class.cv (nb051AlphaDummy004 x y A B C))))))).fv ∪
        ((Class.cab (nb051AlphaDummy003 x y A B C)
            (synWrex (nb051AlphaDummy004 x y A B C) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                (synCphi (Class.cv (nb051AlphaDummy004 x y A B C))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0006 x y A B C) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0006 x y A B C) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0011 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    y ∈
      (((Class.cab (nb051AlphaDummy003 x y A B C) (synWrex (nb051AlphaDummy004 x y A B C)
              (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                (synCphi (Class.cv (nb051AlphaDummy004 x y A B C))))))).fv ∪
        ((Class.cab (nb051AlphaDummy003 x y A B C)
            (synWrex (nb051AlphaDummy004 x y A B C) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                (synCphi (Class.cv (nb051AlphaDummy004 x y A B C))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0007 x y A B C) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0007 x y A B C) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0012 (x : Var) (y : Var) (z : Var) :
    x ∈
      (((Class.cab (nb051AlphaDummy005 x y z)
            (synWrex (nb051AlphaDummy006 x y z) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                (synCphi (Class.cv (nb051AlphaDummy006 x y z))))))).fv ∪
        ((Class.cab (nb051AlphaDummy005 x y z)
            (synWrex (nb051AlphaDummy006 x y z) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                (synCphi (Class.cv (nb051AlphaDummy006 x y z))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0008 x y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0008 x y z) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0013 (x : Var) (y : Var) (z : Var) :
    y ∈
      (((Class.cab (nb051AlphaDummy005 x y z)
            (synWrex (nb051AlphaDummy006 x y z) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                (synCphi (Class.cv (nb051AlphaDummy006 x y z))))))).fv ∪
        ((Class.cab (nb051AlphaDummy005 x y z)
            (synWrex (nb051AlphaDummy006 x y z) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                (synCphi (Class.cv (nb051AlphaDummy006 x y z))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0009 x y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0009 x y z) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0014 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    x ∈
      (((synCcompl (Class.cab (nb051AlphaDummy003 x y A B C)
              (synWrex (nb051AlphaDummy004 x y A B C) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                  (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))))))).fv ∪ ((synCcompl
            (Class.cab (nb051AlphaDummy003 x y A B C)
              (synWrex (nb051AlphaDummy004 x y A B C)
                (Class.cv (nb051AlphaDummy000 x y A B C))
                (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                  (synCun (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := x) (s := ((synCcompl
            (Class.cab (nb051AlphaDummy003 x y A B C)
              (synWrex (nb051AlphaDummy004 x y A B C) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                  (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))))))).fv)
        ((synCcompl (Class.cab (nb051AlphaDummy003 x y A B C)
              (synWrex (nb051AlphaDummy004 x y A B C)
                (Class.cv (nb051AlphaDummy000 x y A B C))
                (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                  (synCun (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))
                    (synCsn (synC0c)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0006 x y A B C) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0006 x y A B C) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0015 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    y ∈
      (((synCcompl (Class.cab (nb051AlphaDummy003 x y A B C)
              (synWrex (nb051AlphaDummy004 x y A B C) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                  (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))))))).fv ∪ ((synCcompl
            (Class.cab (nb051AlphaDummy003 x y A B C)
              (synWrex (nb051AlphaDummy004 x y A B C)
                (Class.cv (nb051AlphaDummy000 x y A B C))
                (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                  (synCun (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := y) (s := ((synCcompl
            (Class.cab (nb051AlphaDummy003 x y A B C)
              (synWrex (nb051AlphaDummy004 x y A B C) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                  (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))))))).fv)
        ((synCcompl (Class.cab (nb051AlphaDummy003 x y A B C)
              (synWrex (nb051AlphaDummy004 x y A B C)
                (Class.cv (nb051AlphaDummy000 x y A B C))
                (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                  (synCun (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))
                    (synCsn (synC0c)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0007 x y A B C) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0007 x y A B C) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0016 (x : Var) (y : Var) (z : Var) :
    x ∈
      (((synCcompl (Class.cab (nb051AlphaDummy005 x y z)
              (synWrex (nb051AlphaDummy006 x y z) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                  (synCphi (Class.cv (nb051AlphaDummy006 x y z)))))))).fv ∪ ((synCcompl
            (Class.cab (nb051AlphaDummy005 x y z)
              (synWrex (nb051AlphaDummy006 x y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                  (synCun (synCphi (Class.cv (nb051AlphaDummy006 x y z)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := x) (s := ((synCcompl (Class.cab (nb051AlphaDummy005 x y z)
              (synWrex (nb051AlphaDummy006 x y z) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                  (synCphi (Class.cv (nb051AlphaDummy006 x y z)))))))).fv)
        ((synCcompl (Class.cab (nb051AlphaDummy005 x y z)
              (synWrex (nb051AlphaDummy006 x y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                  (synCun (synCphi (Class.cv (nb051AlphaDummy006 x y z)))
                    (synCsn (synC0c)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0008 x y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0008 x y z) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0017 (x : Var) (y : Var) (z : Var) :
    y ∈
      (((synCcompl (Class.cab (nb051AlphaDummy005 x y z)
              (synWrex (nb051AlphaDummy006 x y z) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                  (synCphi (Class.cv (nb051AlphaDummy006 x y z)))))))).fv ∪ ((synCcompl
            (Class.cab (nb051AlphaDummy005 x y z)
              (synWrex (nb051AlphaDummy006 x y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                  (synCun (synCphi (Class.cv (nb051AlphaDummy006 x y z)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := y) (s := ((synCcompl (Class.cab (nb051AlphaDummy005 x y z)
              (synWrex (nb051AlphaDummy006 x y z) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                  (synCphi (Class.cv (nb051AlphaDummy006 x y z)))))))).fv)
        ((synCcompl (Class.cab (nb051AlphaDummy005 x y z)
              (synWrex (nb051AlphaDummy006 x y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                  (synCun (synCphi (Class.cv (nb051AlphaDummy006 x y z)))
                    (synCsn (synC0c)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0009 x y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0009 x y z) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0018 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    x ∈ (({ x } : Finset Var) ∪ (A).fv ∪ ({ y } : Finset Var) ∪ (B).fv ∪ (C).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0019 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    y ∈ (({ x } : Finset Var) ∪ (A).fv ∪ ({ y } : Finset Var) ∪ (B).fv ∪ (C).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0020 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy004 x y A B C) ∈
      (((Class.cv (nb051AlphaDummy004 x y A B C))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0021 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy006 x y z) ∈ (((Class.cv (nb051AlphaDummy006 x y z))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0022 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy011 x y A B C) ∈
      (((Wff.classMem (Class.cv (nb051AlphaDummy011 x y A B C)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb051AlphaDummy011 x y A B C)) (synC1c))).fv ∪
        ((Class.cv (nb051AlphaDummy011 x y A B C))).fv) :=
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

theorem nb051_support_mem_0023 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy013 x y z) ∈
      (((Wff.classMem (Class.cv (nb051AlphaDummy013 x y z)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb051AlphaDummy013 x y z)) (synC1c))).fv ∪
        ((Class.cv (nb051AlphaDummy013 x y z))).fv) :=
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

theorem nb051_support_mem_0024 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy011 x y A B C) ∈
      (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0025 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy013 x y z) ∈
      (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0026 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy018 x y A B C) ∈
      (((synCnin (Class.cv (nb051AlphaDummy018 x y A B C))
            (Class.cv (nb051AlphaDummy019 x y A B C)))).fv ∪
        ((synCnin (Class.cv (nb051AlphaDummy018 x y A B C))
            (Class.cv (nb051AlphaDummy019 x y A B C)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0027 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy021 x y z) ∈
      (((synCnin (Class.cv (nb051AlphaDummy021 x y z))
            (Class.cv (nb051AlphaDummy022 x y z)))).fv ∪
        ((synCnin (Class.cv (nb051AlphaDummy021 x y z))
            (Class.cv (nb051AlphaDummy022 x y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0028 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy018 x y A B C) ∈
      (((Class.cv (nb051AlphaDummy018 x y A B C))).fv ∪
        ((Class.cv (nb051AlphaDummy019 x y A B C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0029 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy021 x y z) ∈
      (((Class.cv (nb051AlphaDummy021 x y z))).fv ∪
        ((Class.cv (nb051AlphaDummy022 x y z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0030 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy019 x y A B C) ∈
      (((synCnin (Class.cv (nb051AlphaDummy018 x y A B C))
            (Class.cv (nb051AlphaDummy019 x y A B C)))).fv ∪
        ((synCnin (Class.cv (nb051AlphaDummy018 x y A B C))
            (Class.cv (nb051AlphaDummy019 x y A B C)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0031 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy022 x y z) ∈
      (((synCnin (Class.cv (nb051AlphaDummy021 x y z))
            (Class.cv (nb051AlphaDummy022 x y z)))).fv ∪
        ((synCnin (Class.cv (nb051AlphaDummy021 x y z))
            (Class.cv (nb051AlphaDummy022 x y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0032 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy019 x y A B C) ∈
      (((Class.cv (nb051AlphaDummy018 x y A B C))).fv ∪
        ((Class.cv (nb051AlphaDummy019 x y A B C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0033 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy022 x y z) ∈
      (((Class.cv (nb051AlphaDummy021 x y z))).fv ∪
        ((Class.cv (nb051AlphaDummy022 x y z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0034 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy018 x y A B C) ∈
      (((synCcompl (Class.cv (nb051AlphaDummy018 x y A B C)))).fv ∪
        ((synCcompl (Class.cv (nb051AlphaDummy019 x y A B C)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0035 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy021 x y z) ∈
      (((synCcompl (Class.cv (nb051AlphaDummy021 x y z)))).fv ∪
        ((synCcompl (Class.cv (nb051AlphaDummy022 x y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0036 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy018 x y A B C) ∈
      (((Class.cv (nb051AlphaDummy018 x y A B C))).fv ∪
        ((Class.cv (nb051AlphaDummy018 x y A B C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0037 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy021 x y z) ∈
      (((Class.cv (nb051AlphaDummy021 x y z))).fv ∪
        ((Class.cv (nb051AlphaDummy021 x y z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0038 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy019 x y A B C) ∈
      (((synCcompl (Class.cv (nb051AlphaDummy018 x y A B C)))).fv ∪
        ((synCcompl (Class.cv (nb051AlphaDummy019 x y A B C)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0039 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy022 x y z) ∈
      (((synCcompl (Class.cv (nb051AlphaDummy021 x y z)))).fv ∪
        ((synCcompl (Class.cv (nb051AlphaDummy022 x y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0040 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy019 x y A B C) ∈
      (((Class.cv (nb051AlphaDummy019 x y A B C))).fv ∪
        ((Class.cv (nb051AlphaDummy019 x y A B C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0041 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy022 x y z) ∈
      (((Class.cv (nb051AlphaDummy022 x y z))).fv ∪
        ((Class.cv (nb051AlphaDummy022 x y z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0042 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy000 x y A B C) ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb051AlphaDummy000 x y A B C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0043 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy000 x y A B C) ∈
      (((synCcompl (Class.cab (nb051AlphaDummy003 x y A B C)
              (synWrex (nb051AlphaDummy004 x y A B C) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                  (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))))))).fv ∪ ((synCcompl
            (Class.cab (nb051AlphaDummy003 x y A B C)
              (synWrex (nb051AlphaDummy004 x y A B C)
                (Class.cv (nb051AlphaDummy000 x y A B C))
                (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                  (synCun (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_right (a := (nb051AlphaDummy000 x y A B C)) (t := ((synCcompl
            (Class.cab (nb051AlphaDummy003 x y A B C)
              (synWrex (nb051AlphaDummy004 x y A B C)
                (Class.cv (nb051AlphaDummy000 x y A B C))
                (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                  (synCun (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))
                    (synCsn (synC0c)))))))).fv)
        ((synCcompl (Class.cab (nb051AlphaDummy003 x y A B C)
              (synWrex (nb051AlphaDummy004 x y A B C) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                  (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0042 x y A B C) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0042 x y A B C) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0044 (x : Var) (y : Var) (z : Var) :
    z ∈ (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0045 (x : Var) (y : Var) (z : Var) :
    z ∈
      (((synCcompl (Class.cab (nb051AlphaDummy005 x y z)
              (synWrex (nb051AlphaDummy006 x y z) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                  (synCphi (Class.cv (nb051AlphaDummy006 x y z)))))))).fv ∪ ((synCcompl
            (Class.cab (nb051AlphaDummy005 x y z)
              (synWrex (nb051AlphaDummy006 x y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                  (synCun (synCphi (Class.cv (nb051AlphaDummy006 x y z)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_right (a := z) (t := ((synCcompl
            (Class.cab (nb051AlphaDummy005 x y z)
              (synWrex (nb051AlphaDummy006 x y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                  (synCun (synCphi (Class.cv (nb051AlphaDummy006 x y z)))
                    (synCsn (synC0c)))))))).fv)
        ((synCcompl (Class.cab (nb051AlphaDummy005 x y z)
              (synWrex (nb051AlphaDummy006 x y z) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                  (synCphi (Class.cv (nb051AlphaDummy006 x y z)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0044 x y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0044 x y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0046 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy000 x y A B C) ∈
      (((Class.cab (nb051AlphaDummy003 x y A B C) (synWrex (nb051AlphaDummy004 x y A B C)
              (Class.cv (nb051AlphaDummy000 x y A B C))
              (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                (synCun (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb051AlphaDummy003 x y A B C)
            (synWrex (nb051AlphaDummy004 x y A B C)
              (Class.cv (nb051AlphaDummy000 x y A B C))
              (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
                (synCun (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0042 x y A B C) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0042 x y A B C) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0047 (x : Var) (y : Var) (z : Var) :
    z ∈
      (((Class.cab (nb051AlphaDummy005 x y z)
            (synWrex (nb051AlphaDummy006 x y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                (synCun (synCphi (Class.cv (nb051AlphaDummy006 x y z)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb051AlphaDummy005 x y z)
            (synWrex (nb051AlphaDummy006 x y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
                (synCun (synCphi (Class.cv (nb051AlphaDummy006 x y z)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0044 x y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0044 x y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0048 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy004 x y A B C) ∈
      (((synCcompl (synCphi (Class.cv (nb051AlphaDummy004 x y A B C))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0049 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy006 x y z) ∈
      (((synCcompl (synCphi (Class.cv (nb051AlphaDummy006 x y z))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0050 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy004 x y A B C) ∈
      (((synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))).fv ∪
        ((synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part004`. -/


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

theorem nb051_support_mem_0051 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy006 x y z) ∈
      (((synCphi (Class.cv (nb051AlphaDummy006 x y z)))).fv ∪
        ((synCphi (Class.cv (nb051AlphaDummy006 x y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_wpp_notmem_0000 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy004 x y A B C) ∉ ((synCop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051AlphaDummy004, fv_syn_cop, Finset.mem_union, fv_class_cv,
    Finset.mem_singleton, not_or] using
    (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0006 x y A B C) 1)))
      (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0007 x y A B C) 1))))

theorem nb051_wpp_notmem_0001 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy006 x y z) ∉ ((synCop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051AlphaDummy006, fv_syn_cop, Finset.mem_union, fv_class_cv,
    Finset.mem_singleton, not_or] using
    (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0008 x y z) 1)))
      (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0009 x y z) 1))))

theorem nb051_wpp_notmem_0002 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy003 x y A B C) ∉ ((synCop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051AlphaDummy003, fv_syn_cop, Finset.mem_union, fv_class_cv,
    Finset.mem_singleton, not_or] using
    (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0006 x y A B C) 0)))
      (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0007 x y A B C) 0))))

theorem nb051_wpp_notmem_0003 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy005 x y z) ∉ ((synCop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051AlphaDummy005, fv_syn_cop, Finset.mem_union, fv_class_cv,
    Finset.mem_singleton, not_or] using
    (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0008 x y z) 0)))
      (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0009 x y z) 0))))

theorem nb051_wpp_notmem_0004 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy009 x y A B C) ∉ ((synCop (Class.cv x) (Class.cv y))).fv :=
  by
  have inequality0 : (nb051AlphaDummy009 x y A B C) ≠ x :=
    by
    unfold nb051AlphaDummy009
    with_reducible
      exact
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0010 x y A B C) 0)))
  have inequality1 : (nb051AlphaDummy009 x y A B C) ≠ y :=
    by
    unfold nb051AlphaDummy009
    with_reducible
      exact
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0011 x y A B C) 0)))
  simpa only [fv_syn_cop, Finset.mem_union, fv_class_cv, Finset.mem_singleton,
    not_or] using (And.intro inequality0 inequality1)

theorem nb051_wpp_notmem_0005 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy010 x y z) ∉ ((synCop (Class.cv x) (Class.cv y))).fv :=
  by
  have inequality0 : (nb051AlphaDummy010 x y z) ≠ x :=
    by
    unfold nb051AlphaDummy010
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0012 x y z) 0)))
  have inequality1 : (nb051AlphaDummy010 x y z) ≠ y :=
    by
    unfold nb051AlphaDummy010
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0013 x y z) 0)))
  simpa only [fv_syn_cop, Finset.mem_union, fv_class_cv, Finset.mem_singleton,
    not_or] using (And.intro inequality0 inequality1)

theorem nb051_wpp_notmem_0006 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy007 x y A B C) ∉ ((synCop (Class.cv x) (Class.cv y))).fv :=
  by
  have inequality0 : (nb051AlphaDummy007 x y A B C) ≠ x :=
    by
    unfold nb051AlphaDummy007
    with_reducible
      exact
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0014 x y A B C) 0)))
  have inequality1 : (nb051AlphaDummy007 x y A B C) ≠ y :=
    by
    unfold nb051AlphaDummy007
    with_reducible
      exact
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0015 x y A B C) 0)))
  simpa only [fv_syn_cop, Finset.mem_union, fv_class_cv, Finset.mem_singleton,
    not_or] using (And.intro inequality0 inequality1)

theorem nb051_wpp_notmem_0007 (x : Var) (y : Var) (z : Var) :
    (nb051AlphaDummy008 x y z) ∉ ((synCop (Class.cv x) (Class.cv y))).fv :=
  by
  have inequality0 : (nb051AlphaDummy008 x y z) ≠ x :=
    by
    unfold nb051AlphaDummy008
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0016 x y z) 0)))
  have inequality1 : (nb051AlphaDummy008 x y z) ≠ y :=
    by
    unfold nb051AlphaDummy008
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0017 x y z) 0)))
  simpa only [fv_syn_cop, Finset.mem_union, fv_class_cv, Finset.mem_singleton,
    not_or] using (And.intro inequality0 inequality1)

theorem nb051_compact_fv_empty_0008 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : (nb051AlphaDummy000 x y A B C) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0008 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy000 x y A B C) ∉ ((synCop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051AlphaDummy000, fv_syn_cop, Finset.mem_union, fv_class_cv,
    Finset.mem_singleton, not_or] using
    (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0018 x y A B C) 0)))
      (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0019 x y A B C) 0))))

theorem nb051_compact_fv_empty_0009 (z : Var) : z ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0009 (x : Var) (y : Var) (z : Var) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) : z ∉ ((synCop (Class.cv x) (Class.cv y))).fv := by
  simp only [fv_syn_cop, Finset.mem_union, fv_class_cv, (Ne.symm dv_x_z),
    Finset.mem_singleton, (Ne.symm dv_y_z), or_false, not_false_eq_true]

theorem nb051_compact_fv_empty_0010 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : (nb051AlphaDummy001 x y A B C) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0010 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy001 x y A B C) ∉ ((synCop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051AlphaDummy001, fv_syn_cop, Finset.mem_union, fv_class_cv,
    Finset.mem_singleton, not_or] using
    (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0000 x y A B C) 0)))
      (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0002 x y A B C) 0))))

theorem nb051_compact_fv_empty_0011 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) : (nb051AlphaDummy002 x y z A B C) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0011 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) :
    (nb051AlphaDummy002 x y z A B C) ∉ ((synCop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051AlphaDummy002, fv_syn_cop, Finset.mem_union, fv_class_cv,
    Finset.mem_singleton, not_or] using
    (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0001 x y z A B C) 0)))
      (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0003 x y z A B C) 0))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part005`. -/


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

theorem nb051_compact_envfresh_0000 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    TEnvFresh
      [((nb051AlphaDummy004 x y A B C), (nb051AlphaDummy006 x y z)),
        ((nb051AlphaDummy003 x y A B C), (nb051AlphaDummy005 x y z)),
        ((nb051AlphaDummy009 x y A B C), (nb051AlphaDummy010 x y z)),
        ((nb051AlphaDummy007 x y A B C), (nb051AlphaDummy008 x y z)),
        ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
        ((nb051AlphaDummy001 x y A B C), (nb051AlphaDummy002 x y z A B C))]
      ((synCop (Class.cv x) (Class.cv y))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb051AlphaDummy004 x y A B C) (nb051AlphaDummy006 x y z)
      (nb051_wpp_notmem_0000 x y A B C) (nb051_wpp_notmem_0001 x y z)
      (TEnvFresh.consFresh (nb051AlphaDummy003 x y A B C) (nb051AlphaDummy005 x y z)
        (nb051_wpp_notmem_0002 x y A B C) (nb051_wpp_notmem_0003 x y z)
        (TEnvFresh.consFresh (nb051AlphaDummy009 x y A B C)
          (nb051AlphaDummy010 x y z) (nb051_wpp_notmem_0004 x y A B C)
          (nb051_wpp_notmem_0005 x y z) (TEnvFresh.consFresh (nb051AlphaDummy007 x y A B C)
            (nb051AlphaDummy008 x y z) (nb051_wpp_notmem_0006 x y A B C)
            (nb051_wpp_notmem_0007 x y z)
            (TEnvFresh.consFresh (nb051AlphaDummy000 x y A B C) z
              (nb051_wpp_notmem_0008 x y A B C) (nb051_wpp_notmem_0009 x y z dv_x_z dv_y_z)
              (TEnvFresh.consSame y (TEnvFresh.consSame x
                  (TEnvFresh.consFresh (nb051AlphaDummy001 x y A B C)
                    (nb051AlphaDummy002 x y z A B C) (nb051_wpp_notmem_0010 x y A B C)
                    (nb051_wpp_notmem_0011 x y z A B C)
                    (TEnvFresh.nil ((synCop (Class.cv x) (Class.cv y))).fv)))))))))

/-- Checked nominal proof certificate identified upstream as `nb051_wpp_refl_0000`. -/
@[expose]
noncomputable def nb051WppRefl0000 (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    TReflOn
      [((nb051AlphaDummy004 x y A B C), (nb051AlphaDummy006 x y z)),
        ((nb051AlphaDummy003 x y A B C), (nb051AlphaDummy005 x y z)),
        ((nb051AlphaDummy009 x y A B C), (nb051AlphaDummy010 x y z)),
        ((nb051AlphaDummy007 x y A B C), (nb051AlphaDummy008 x y z)),
        ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
        ((nb051AlphaDummy001 x y A B C), (nb051AlphaDummy002 x y z A B C))]
      ((synCop (Class.cv x) (Class.cv y))).fv :=
  TEnvFresh.reflOn (nb051_compact_envfresh_0000 x y z A B C dv_x_z dv_y_z)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
