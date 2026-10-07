/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part001

/-! NF weak partition development: NAR4H5C095M3Part002. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_450`. -/
@[expose]
noncomputable def nb095AlphaDummy450 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy447 f))
          (Class.cv (nb095AlphaDummy448 f)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy447 f)) (Class.cv (nb095AlphaDummy448 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_451`. -/
@[expose]
noncomputable def nb095AlphaDummy451 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy444 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy445 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_452`. -/
@[expose]
noncomputable def nb095AlphaDummy452 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy447 f))).fv ∪
      ((Class.cv (nb095AlphaDummy448 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_453`. -/
@[expose]
noncomputable def nb095AlphaDummy453 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy444 D R S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy445 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_454`. -/
@[expose]
noncomputable def nb095AlphaDummy454 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy447 f)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy448 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_455`. -/
@[expose]
noncomputable def nb095AlphaDummy455 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy444 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy444 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_456`. -/
@[expose]
noncomputable def nb095AlphaDummy456 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy447 f))).fv ∪
      ((Class.cv (nb095AlphaDummy447 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_457`. -/
@[expose]
noncomputable def nb095AlphaDummy457 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy445 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy445 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_458`. -/
@[expose]
noncomputable def nb095AlphaDummy458 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy448 f))).fv ∪
      ((Class.cv (nb095AlphaDummy448 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_459`. -/
@[expose]
noncomputable def nb095AlphaDummy459 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy429 D R S_cls E)
          (synWrex (nb095AlphaDummy430 D R S_cls E)
            (Class.cv (nb095AlphaDummy387 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy429 D R S_cls E)
          (synWrex (nb095AlphaDummy430 D R S_cls E)
            (Class.cv (nb095AlphaDummy387 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_460`. -/
@[expose]
noncomputable def nb095AlphaDummy460 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy431 f)
          (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy390 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy432 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy431 f)
          (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy390 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy432 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_461`. -/
@[expose]
noncomputable def nb095AlphaDummy461 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_462`. -/
@[expose]
noncomputable def nb095AlphaDummy462 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy432 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_463`. -/
@[expose]
noncomputable def nb095AlphaDummy463 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_464`. -/
@[expose]
noncomputable def nb095AlphaDummy464 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy432 f)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy432 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_465`. -/
@[expose]
noncomputable def nb095AlphaDummy465 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_466`. -/
@[expose]
noncomputable def nb095AlphaDummy466 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_467`. -/
@[expose]
noncomputable def nb095AlphaDummy467 (f : Var) : Var :=
  (freshVar (((synCcnv (Class.cv f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_468`. -/
@[expose]
noncomputable def nb095AlphaDummy468 (f : Var) : Var :=
  (freshVar (((synCcnv (Class.cv f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_469`. -/
@[expose]
noncomputable def nb095AlphaDummy469 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (({(nb095AlphaDummy465 D R S_cls E)} : Finset Var) ∪
        ({(nb095AlphaDummy466 D R S_cls E)} : Finset Var) ∪
      ((synWbr (Class.cv (nb095AlphaDummy466 D R S_cls E))
          (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
          (Class.cv (nb095AlphaDummy465 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_470`. -/
@[expose]
noncomputable def nb095AlphaDummy470 (f : Var) : Var :=
  (freshVar (({(nb095AlphaDummy467 f)} : Finset Var) ∪
        ({(nb095AlphaDummy468 f)} : Finset Var) ∪
      ((synWbr (Class.cv (nb095AlphaDummy468 f)) (synCcnv (Class.cv f))
          (Class.cv (nb095AlphaDummy467 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_471`. -/
@[expose]
noncomputable def nb095AlphaDummy471 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_472`. -/
@[expose]
noncomputable def nb095AlphaDummy472 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_473`. -/
@[expose]
noncomputable def nb095AlphaDummy473 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy467 f))).fv ∪
      ((Class.cv (nb095AlphaDummy468 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_474`. -/
@[expose]
noncomputable def nb095AlphaDummy474 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy467 f))).fv ∪
      ((Class.cv (nb095AlphaDummy468 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_475`. -/
@[expose]
noncomputable def nb095AlphaDummy475 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy471 D R S_cls E)
            (synWrex (nb095AlphaDummy472 D R S_cls E)
              (Class.cv (nb095AlphaDummy465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy471 D R S_cls E)
            (synWrex (nb095AlphaDummy472 D R S_cls E)
              (Class.cv (nb095AlphaDummy466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_476`. -/
@[expose]
noncomputable def nb095AlphaDummy476 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy473 f)
            (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy467 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                (synCphi (Class.cv (nb095AlphaDummy474 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy473 f)
            (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy468 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy474 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_477`. -/
@[expose]
noncomputable def nb095AlphaDummy477 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy471 D R S_cls E)
          (synWrex (nb095AlphaDummy472 D R S_cls E)
            (Class.cv (nb095AlphaDummy465 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy471 D R S_cls E)
          (synWrex (nb095AlphaDummy472 D R S_cls E)
            (Class.cv (nb095AlphaDummy465 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_478`. -/
@[expose]
noncomputable def nb095AlphaDummy478 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy473 f)
          (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy467 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
              (synCphi (Class.cv (nb095AlphaDummy474 f))))))).fv ∪
      ((Class.cab (nb095AlphaDummy473 f)
          (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy467 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
              (synCphi (Class.cv (nb095AlphaDummy474 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_479`. -/
@[expose]
noncomputable def nb095AlphaDummy479 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy472 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_480`. -/
@[expose]
noncomputable def nb095AlphaDummy480 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy472 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_481`. -/
@[expose]
noncomputable def nb095AlphaDummy481 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy474 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_482`. -/
@[expose]
noncomputable def nb095AlphaDummy482 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy474 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_483`. -/
@[expose]
noncomputable def nb095AlphaDummy483 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy479 D R S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy479 D R S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy479 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_484`. -/
@[expose]
noncomputable def nb095AlphaDummy484 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy481 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy481 f)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy481 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_485`. -/
@[expose]
noncomputable def nb095AlphaDummy485 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy479 D R S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_486`. -/
@[expose]
noncomputable def nb095AlphaDummy486 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy479 D R S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_487`. -/
@[expose]
noncomputable def nb095AlphaDummy487 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy479 D R S_cls E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_488`. -/
@[expose]
noncomputable def nb095AlphaDummy488 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_489`. -/
@[expose]
noncomputable def nb095AlphaDummy489 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_490`. -/
@[expose]
noncomputable def nb095AlphaDummy490 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_491`. -/
@[expose]
noncomputable def nb095AlphaDummy491 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy486 D R S_cls E))
          (Class.cv (nb095AlphaDummy487 D R S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy486 D R S_cls E))
          (Class.cv (nb095AlphaDummy487 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_492`. -/
@[expose]
noncomputable def nb095AlphaDummy492 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy489 f))
          (Class.cv (nb095AlphaDummy490 f)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy489 f)) (Class.cv (nb095AlphaDummy490 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_493`. -/
@[expose]
noncomputable def nb095AlphaDummy493 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy486 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy487 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_494`. -/
@[expose]
noncomputable def nb095AlphaDummy494 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy489 f))).fv ∪
      ((Class.cv (nb095AlphaDummy490 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_495`. -/
@[expose]
noncomputable def nb095AlphaDummy495 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy486 D R S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy487 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_496`. -/
@[expose]
noncomputable def nb095AlphaDummy496 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy489 f)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy490 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_497`. -/
@[expose]
noncomputable def nb095AlphaDummy497 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy486 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy486 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_498`. -/
@[expose]
noncomputable def nb095AlphaDummy498 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy489 f))).fv ∪
      ((Class.cv (nb095AlphaDummy489 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_499`. -/
@[expose]
noncomputable def nb095AlphaDummy499 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy487 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy487 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_500`. -/
@[expose]
noncomputable def nb095AlphaDummy500 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy490 f))).fv ∪
      ((Class.cv (nb095AlphaDummy490 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_501`. -/
@[expose]
noncomputable def nb095AlphaDummy501 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy471 D R S_cls E)
          (synWrex (nb095AlphaDummy472 D R S_cls E)
            (Class.cv (nb095AlphaDummy466 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy471 D R S_cls E)
          (synWrex (nb095AlphaDummy472 D R S_cls E)
            (Class.cv (nb095AlphaDummy466 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_502`. -/
@[expose]
noncomputable def nb095AlphaDummy502 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy473 f)
          (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy468 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy474 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy473 f)
          (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy468 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy474 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_503`. -/
@[expose]
noncomputable def nb095AlphaDummy503 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_504`. -/
@[expose]
noncomputable def nb095AlphaDummy504 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy474 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_505`. -/
@[expose]
noncomputable def nb095AlphaDummy505 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_506`. -/
@[expose]
noncomputable def nb095AlphaDummy506 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy474 f)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy474 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_507`. -/
@[expose]
noncomputable def nb095AlphaDummy507 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_508`. -/
@[expose]
noncomputable def nb095AlphaDummy508 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_509`. -/
@[expose]
noncomputable def nb095AlphaDummy509 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy468 f))).fv ∪
      ((Class.cv (nb095AlphaDummy467 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_510`. -/
@[expose]
noncomputable def nb095AlphaDummy510 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy468 f))).fv ∪
      ((Class.cv (nb095AlphaDummy467 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_511`. -/
@[expose]
noncomputable def nb095AlphaDummy511 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy507 D R S_cls E)
            (synWrex (nb095AlphaDummy508 D R S_cls E)
              (Class.cv (nb095AlphaDummy466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy507 D R S_cls E)
            (synWrex (nb095AlphaDummy508 D R S_cls E)
              (Class.cv (nb095AlphaDummy465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_512`. -/
@[expose]
noncomputable def nb095AlphaDummy512 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy509 f)
            (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy468 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                (synCphi (Class.cv (nb095AlphaDummy510 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy509 f)
            (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy467 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy510 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_513`. -/
@[expose]
noncomputable def nb095AlphaDummy513 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy507 D R S_cls E)
          (synWrex (nb095AlphaDummy508 D R S_cls E)
            (Class.cv (nb095AlphaDummy466 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy507 D R S_cls E)
          (synWrex (nb095AlphaDummy508 D R S_cls E)
            (Class.cv (nb095AlphaDummy466 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_514`. -/
@[expose]
noncomputable def nb095AlphaDummy514 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy509 f)
          (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy468 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
              (synCphi (Class.cv (nb095AlphaDummy510 f))))))).fv ∪
      ((Class.cab (nb095AlphaDummy509 f)
          (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy468 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
              (synCphi (Class.cv (nb095AlphaDummy510 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_515`. -/
@[expose]
noncomputable def nb095AlphaDummy515 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy508 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_516`. -/
@[expose]
noncomputable def nb095AlphaDummy516 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy508 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_517`. -/
@[expose]
noncomputable def nb095AlphaDummy517 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy510 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_518`. -/
@[expose]
noncomputable def nb095AlphaDummy518 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy510 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_519`. -/
@[expose]
noncomputable def nb095AlphaDummy519 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy515 D R S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy515 D R S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy515 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_520`. -/
@[expose]
noncomputable def nb095AlphaDummy520 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy517 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy517 f)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy517 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_521`. -/
@[expose]
noncomputable def nb095AlphaDummy521 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy515 D R S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_522`. -/
@[expose]
noncomputable def nb095AlphaDummy522 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy515 D R S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_523`. -/
@[expose]
noncomputable def nb095AlphaDummy523 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy515 D R S_cls E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_524`. -/
@[expose]
noncomputable def nb095AlphaDummy524 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_525`. -/
@[expose]
noncomputable def nb095AlphaDummy525 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_526`. -/
@[expose]
noncomputable def nb095AlphaDummy526 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_527`. -/
@[expose]
noncomputable def nb095AlphaDummy527 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy522 D R S_cls E))
          (Class.cv (nb095AlphaDummy523 D R S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy522 D R S_cls E))
          (Class.cv (nb095AlphaDummy523 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_528`. -/
@[expose]
noncomputable def nb095AlphaDummy528 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy525 f))
          (Class.cv (nb095AlphaDummy526 f)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy525 f)) (Class.cv (nb095AlphaDummy526 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_529`. -/
@[expose]
noncomputable def nb095AlphaDummy529 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy522 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy523 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_530`. -/
@[expose]
noncomputable def nb095AlphaDummy530 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy525 f))).fv ∪
      ((Class.cv (nb095AlphaDummy526 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_531`. -/
@[expose]
noncomputable def nb095AlphaDummy531 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy522 D R S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy523 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_532`. -/
@[expose]
noncomputable def nb095AlphaDummy532 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy525 f)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy526 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_533`. -/
@[expose]
noncomputable def nb095AlphaDummy533 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy522 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy522 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_534`. -/
@[expose]
noncomputable def nb095AlphaDummy534 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy525 f))).fv ∪
      ((Class.cv (nb095AlphaDummy525 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_535`. -/
@[expose]
noncomputable def nb095AlphaDummy535 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy523 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy523 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_536`. -/
@[expose]
noncomputable def nb095AlphaDummy536 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy526 f))).fv ∪
      ((Class.cv (nb095AlphaDummy526 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_537`. -/
@[expose]
noncomputable def nb095AlphaDummy537 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy507 D R S_cls E)
          (synWrex (nb095AlphaDummy508 D R S_cls E)
            (Class.cv (nb095AlphaDummy465 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy507 D R S_cls E)
          (synWrex (nb095AlphaDummy508 D R S_cls E)
            (Class.cv (nb095AlphaDummy465 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_538`. -/
@[expose]
noncomputable def nb095AlphaDummy538 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy509 f)
          (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy467 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy510 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy509 f)
          (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy467 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy510 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_539`. -/
@[expose]
noncomputable def nb095AlphaDummy539 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_540`. -/
@[expose]
noncomputable def nb095AlphaDummy540 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy510 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_541`. -/
@[expose]
noncomputable def nb095AlphaDummy541 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_542`. -/
@[expose]
noncomputable def nb095AlphaDummy542 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy510 f)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy510 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_543`. -/
@[expose]
noncomputable def nb095AlphaDummy543 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_544`. -/
@[expose]
noncomputable def nb095AlphaDummy544 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_545`. -/
@[expose]
noncomputable def nb095AlphaDummy545 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy390 f))).fv ∪
      ((Class.cv (nb095AlphaDummy389 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_546`. -/
@[expose]
noncomputable def nb095AlphaDummy546 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy390 f))).fv ∪
      ((Class.cv (nb095AlphaDummy389 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_547`. -/
@[expose]
noncomputable def nb095AlphaDummy547 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy543 D R S_cls E)
            (synWrex (nb095AlphaDummy544 D R S_cls E)
              (Class.cv (nb095AlphaDummy387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy543 D R S_cls E)
            (synWrex (nb095AlphaDummy544 D R S_cls E)
              (Class.cv (nb095AlphaDummy386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_548`. -/
@[expose]
noncomputable def nb095AlphaDummy548 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy545 f)
            (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy390 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                (synCphi (Class.cv (nb095AlphaDummy546 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy545 f)
            (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy389 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy546 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_549`. -/
@[expose]
noncomputable def nb095AlphaDummy549 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy543 D R S_cls E)
          (synWrex (nb095AlphaDummy544 D R S_cls E)
            (Class.cv (nb095AlphaDummy387 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy543 D R S_cls E)
          (synWrex (nb095AlphaDummy544 D R S_cls E)
            (Class.cv (nb095AlphaDummy387 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_550`. -/
@[expose]
noncomputable def nb095AlphaDummy550 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy545 f)
          (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy390 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
              (synCphi (Class.cv (nb095AlphaDummy546 f))))))).fv ∪
      ((Class.cab (nb095AlphaDummy545 f)
          (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy390 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
              (synCphi (Class.cv (nb095AlphaDummy546 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_551`. -/
@[expose]
noncomputable def nb095AlphaDummy551 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy544 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_552`. -/
@[expose]
noncomputable def nb095AlphaDummy552 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy544 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_553`. -/
@[expose]
noncomputable def nb095AlphaDummy553 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy546 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_554`. -/
@[expose]
noncomputable def nb095AlphaDummy554 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy546 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_555`. -/
@[expose]
noncomputable def nb095AlphaDummy555 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy551 D R S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy551 D R S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy551 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_556`. -/
@[expose]
noncomputable def nb095AlphaDummy556 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy553 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy553 f)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy553 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_557`. -/
@[expose]
noncomputable def nb095AlphaDummy557 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_558`. -/
@[expose]
noncomputable def nb095AlphaDummy558 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_559`. -/
@[expose]
noncomputable def nb095AlphaDummy559 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_560`. -/
@[expose]
noncomputable def nb095AlphaDummy560 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_561`. -/
@[expose]
noncomputable def nb095AlphaDummy561 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_562`. -/
@[expose]
noncomputable def nb095AlphaDummy562 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_563`. -/
@[expose]
noncomputable def nb095AlphaDummy563 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy558 D R S_cls E))
          (Class.cv (nb095AlphaDummy559 D R S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy558 D R S_cls E))
          (Class.cv (nb095AlphaDummy559 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_564`. -/
@[expose]
noncomputable def nb095AlphaDummy564 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy561 f))
          (Class.cv (nb095AlphaDummy562 f)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy561 f)) (Class.cv (nb095AlphaDummy562 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_565`. -/
@[expose]
noncomputable def nb095AlphaDummy565 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy558 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy559 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_566`. -/
@[expose]
noncomputable def nb095AlphaDummy566 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy561 f))).fv ∪
      ((Class.cv (nb095AlphaDummy562 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_567`. -/
@[expose]
noncomputable def nb095AlphaDummy567 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy558 D R S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy559 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_568`. -/
@[expose]
noncomputable def nb095AlphaDummy568 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy561 f)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy562 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_569`. -/
@[expose]
noncomputable def nb095AlphaDummy569 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy558 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy558 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_570`. -/
@[expose]
noncomputable def nb095AlphaDummy570 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy561 f))).fv ∪
      ((Class.cv (nb095AlphaDummy561 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_571`. -/
@[expose]
noncomputable def nb095AlphaDummy571 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy559 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy559 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_572`. -/
@[expose]
noncomputable def nb095AlphaDummy572 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy562 f))).fv ∪
      ((Class.cv (nb095AlphaDummy562 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_573`. -/
@[expose]
noncomputable def nb095AlphaDummy573 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy543 D R S_cls E)
          (synWrex (nb095AlphaDummy544 D R S_cls E)
            (Class.cv (nb095AlphaDummy386 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy543 D R S_cls E)
          (synWrex (nb095AlphaDummy544 D R S_cls E)
            (Class.cv (nb095AlphaDummy386 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_574`. -/
@[expose]
noncomputable def nb095AlphaDummy574 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy545 f)
          (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy389 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy546 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy545 f)
          (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy389 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy546 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_575`. -/
@[expose]
noncomputable def nb095AlphaDummy575 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_576`. -/
@[expose]
noncomputable def nb095AlphaDummy576 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy546 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_577`. -/
@[expose]
noncomputable def nb095AlphaDummy577 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_578`. -/
@[expose]
noncomputable def nb095AlphaDummy578 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy546 f)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy546 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_579`. -/
@[expose]
noncomputable def nb095AlphaDummy579 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_580`. -/
@[expose]
noncomputable def nb095AlphaDummy580 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_581`. -/
@[expose]
noncomputable def nb095AlphaDummy581 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_582`. -/
@[expose]
noncomputable def nb095AlphaDummy582 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_583`. -/
@[expose]
noncomputable def nb095AlphaDummy583 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy579 D R S_cls E)
            (synWrex (nb095AlphaDummy580 D R S_cls E)
              (Class.cv (nb095AlphaDummy003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy579 D R S_cls E)
            (synWrex (nb095AlphaDummy580 D R S_cls E)
              (Class.cv (nb095AlphaDummy004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_584`. -/
@[expose]
noncomputable def nb095AlphaDummy584 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))))))).fv ∪
      ((synCcompl (Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_585`. -/
@[expose]
noncomputable def nb095AlphaDummy585 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy579 D R S_cls E)
          (synWrex (nb095AlphaDummy580 D R S_cls E)
            (Class.cv (nb095AlphaDummy003 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy579 D R S_cls E)
          (synWrex (nb095AlphaDummy580 D R S_cls E)
            (Class.cv (nb095AlphaDummy003 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_586`. -/
@[expose]
noncomputable def nb095AlphaDummy586 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
          (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
            (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
              (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
          (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
            (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
              (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_587`. -/
@[expose]
noncomputable def nb095AlphaDummy587 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy580 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_588`. -/
@[expose]
noncomputable def nb095AlphaDummy588 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy580 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_589`. -/
@[expose]
noncomputable def nb095AlphaDummy589 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy582 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_590`. -/
@[expose]
noncomputable def nb095AlphaDummy590 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy582 x u D R S_cls f E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_591`. -/
@[expose]
noncomputable def nb095AlphaDummy591 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy587 D R S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy587 D R S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy587 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_592`. -/
@[expose]
noncomputable def nb095AlphaDummy592 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar
    (((Wff.classMem (Class.cv (nb095AlphaDummy589 x u D R S_cls f E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy589 x u D R S_cls f E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_593`. -/
@[expose]
noncomputable def nb095AlphaDummy593 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_594`. -/
@[expose]
noncomputable def nb095AlphaDummy594 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_595`. -/
@[expose]
noncomputable def nb095AlphaDummy595 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_596`. -/
@[expose]
noncomputable def nb095AlphaDummy596 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_597`. -/
@[expose]
noncomputable def nb095AlphaDummy597 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_598`. -/
@[expose]
noncomputable def nb095AlphaDummy598 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_599`. -/
@[expose]
noncomputable def nb095AlphaDummy599 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy594 D R S_cls E))
          (Class.cv (nb095AlphaDummy595 D R S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy594 D R S_cls E))
          (Class.cv (nb095AlphaDummy595 D R S_cls E)))).fv) 0)

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

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_600`. -/
@[expose]
noncomputable def nb095AlphaDummy600 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy597 x u D R S_cls f E))
          (Class.cv (nb095AlphaDummy598 x u D R S_cls f E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy597 x u D R S_cls f E))
          (Class.cv (nb095AlphaDummy598 x u D R S_cls f E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_601`. -/
@[expose]
noncomputable def nb095AlphaDummy601 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy594 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy595 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_602`. -/
@[expose]
noncomputable def nb095AlphaDummy602 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy597 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095AlphaDummy598 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_603`. -/
@[expose]
noncomputable def nb095AlphaDummy603 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy594 D R S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy595 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_604`. -/
@[expose]
noncomputable def nb095AlphaDummy604 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy597 x u D R S_cls f E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy598 x u D R S_cls f E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_605`. -/
@[expose]
noncomputable def nb095AlphaDummy605 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy594 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy594 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_606`. -/
@[expose]
noncomputable def nb095AlphaDummy606 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy597 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095AlphaDummy597 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_607`. -/
@[expose]
noncomputable def nb095AlphaDummy607 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy595 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy595 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_608`. -/
@[expose]
noncomputable def nb095AlphaDummy608 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy598 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095AlphaDummy598 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_609`. -/
@[expose]
noncomputable def nb095AlphaDummy609 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy579 D R S_cls E)
          (synWrex (nb095AlphaDummy580 D R S_cls E)
            (Class.cv (nb095AlphaDummy004 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy579 D R S_cls E)
          (synWrex (nb095AlphaDummy580 D R S_cls E)
            (Class.cv (nb095AlphaDummy004 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_610`. -/
@[expose]
noncomputable def nb095AlphaDummy610 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
          (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
            (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))
                (synCsn (synC0c))))))).fv ∪
      ((Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
          (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
            (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_611`. -/
@[expose]
noncomputable def nb095AlphaDummy611 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_612`. -/
@[expose]
noncomputable def nb095AlphaDummy612 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_613`. -/
@[expose]
noncomputable def nb095AlphaDummy613 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_614`. -/
@[expose]
noncomputable def nb095AlphaDummy614 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_615`. -/
@[expose]
noncomputable def nb095AlphaDummy615 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪ ((synCnin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_616`. -/
@[expose]
noncomputable def nb095AlphaDummy616 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((synCnin R (synCxp (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))) (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))).fv ∪
      ((synCnin R (synCxp (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))) (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_617`. -/
@[expose]
noncomputable def nb095AlphaDummy617 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar ((R).fv ∪ ((synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_618`. -/
@[expose]
noncomputable def nb095AlphaDummy618 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ ((synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_619`. -/
@[expose]
noncomputable def nb095AlphaDummy619 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_620`. -/
@[expose]
noncomputable def nb095AlphaDummy620 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_621`. -/
@[expose]
noncomputable def nb095AlphaDummy621 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((synCin D
          (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪ ((synCin D
          (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_622`. -/
@[expose]
noncomputable def nb095AlphaDummy622 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((synCin D
          (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪ ((synCin D
          (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_623`. -/
@[expose]
noncomputable def nb095AlphaDummy623 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (({(nb095AlphaDummy619 D R S_cls E)} : Finset Var) ∪
        ({(nb095AlphaDummy620 D R S_cls E)} : Finset Var) ∪ ((synWa
          (Wff.classMem (Class.cv (nb095AlphaDummy619 D R S_cls E)) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))
          (Wff.classMem (Class.cv (nb095AlphaDummy620 D R S_cls E)) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_624`. -/
@[expose]
noncomputable def nb095AlphaDummy624 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (({(nb095AlphaDummy621 x D R)} : Finset Var) ∪
        ({(nb095AlphaDummy622 x D R)} : Finset Var) ∪ ((synWa
          (Wff.classMem (Class.cv (nb095AlphaDummy621 x D R)) (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))))
          (Wff.classMem (Class.cv (nb095AlphaDummy622 x D R)) (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_625`. -/
@[expose]
noncomputable def nb095AlphaDummy625 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy619 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy620 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_626`. -/
@[expose]
noncomputable def nb095AlphaDummy626 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy619 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy620 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_627`. -/
@[expose]
noncomputable def nb095AlphaDummy627 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy621 x D R))).fv ∪
      ((Class.cv (nb095AlphaDummy622 x D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_628`. -/
@[expose]
noncomputable def nb095AlphaDummy628 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy621 x D R))).fv ∪
      ((Class.cv (nb095AlphaDummy622 x D R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_629`. -/
@[expose]
noncomputable def nb095AlphaDummy629 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy625 D R S_cls E)
            (synWrex (nb095AlphaDummy626 D R S_cls E)
              (Class.cv (nb095AlphaDummy619 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy625 D R S_cls E)
            (synWrex (nb095AlphaDummy626 D R S_cls E)
              (Class.cv (nb095AlphaDummy620 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_630`. -/
@[expose]
noncomputable def nb095AlphaDummy630 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy627 x D R)
            (synWrex (nb095AlphaDummy628 x D R) (Class.cv (nb095AlphaDummy621 x D R))
              (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                (synCphi (Class.cv (nb095AlphaDummy628 x D R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy627 x D R) (synWrex (nb095AlphaDummy628 x D R)
              (Class.cv (nb095AlphaDummy622 x D R))
              (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                (synCun (synCphi (Class.cv (nb095AlphaDummy628 x D R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_631`. -/
@[expose]
noncomputable def nb095AlphaDummy631 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy625 D R S_cls E)
          (synWrex (nb095AlphaDummy626 D R S_cls E)
            (Class.cv (nb095AlphaDummy619 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy625 D R S_cls E)
          (synWrex (nb095AlphaDummy626 D R S_cls E)
            (Class.cv (nb095AlphaDummy619 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_632`. -/
@[expose]
noncomputable def nb095AlphaDummy632 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy627 x D R)
          (synWrex (nb095AlphaDummy628 x D R) (Class.cv (nb095AlphaDummy621 x D R))
            (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
              (synCphi (Class.cv (nb095AlphaDummy628 x D R))))))).fv ∪
      ((Class.cab (nb095AlphaDummy627 x D R)
          (synWrex (nb095AlphaDummy628 x D R) (Class.cv (nb095AlphaDummy621 x D R))
            (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
              (synCphi (Class.cv (nb095AlphaDummy628 x D R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_633`. -/
@[expose]
noncomputable def nb095AlphaDummy633 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy626 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_634`. -/
@[expose]
noncomputable def nb095AlphaDummy634 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy626 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_635`. -/
@[expose]
noncomputable def nb095AlphaDummy635 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy628 x D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_636`. -/
@[expose]
noncomputable def nb095AlphaDummy636 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy628 x D R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_637`. -/
@[expose]
noncomputable def nb095AlphaDummy637 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy633 D R S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy633 D R S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy633 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_638`. -/
@[expose]
noncomputable def nb095AlphaDummy638 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy635 x D R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy635 x D R)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy635 x D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_639`. -/
@[expose]
noncomputable def nb095AlphaDummy639 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy633 D R S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_640`. -/
@[expose]
noncomputable def nb095AlphaDummy640 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy633 D R S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_641`. -/
@[expose]
noncomputable def nb095AlphaDummy641 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy633 D R S_cls E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_642`. -/
@[expose]
noncomputable def nb095AlphaDummy642 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_643`. -/
@[expose]
noncomputable def nb095AlphaDummy643 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_644`. -/
@[expose]
noncomputable def nb095AlphaDummy644 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_645`. -/
@[expose]
noncomputable def nb095AlphaDummy645 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy640 D R S_cls E))
          (Class.cv (nb095AlphaDummy641 D R S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy640 D R S_cls E))
          (Class.cv (nb095AlphaDummy641 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_646`. -/
@[expose]
noncomputable def nb095AlphaDummy646 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy643 x D R))
          (Class.cv (nb095AlphaDummy644 x D R)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy643 x D R))
          (Class.cv (nb095AlphaDummy644 x D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_647`. -/
@[expose]
noncomputable def nb095AlphaDummy647 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy640 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy641 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_648`. -/
@[expose]
noncomputable def nb095AlphaDummy648 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy643 x D R))).fv ∪
      ((Class.cv (nb095AlphaDummy644 x D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_649`. -/
@[expose]
noncomputable def nb095AlphaDummy649 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy640 D R S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy641 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_650`. -/
@[expose]
noncomputable def nb095AlphaDummy650 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy643 x D R)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy644 x D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_651`. -/
@[expose]
noncomputable def nb095AlphaDummy651 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy640 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy640 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_652`. -/
@[expose]
noncomputable def nb095AlphaDummy652 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy643 x D R))).fv ∪
      ((Class.cv (nb095AlphaDummy643 x D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_653`. -/
@[expose]
noncomputable def nb095AlphaDummy653 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy641 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy641 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_654`. -/
@[expose]
noncomputable def nb095AlphaDummy654 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy644 x D R))).fv ∪
      ((Class.cv (nb095AlphaDummy644 x D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_655`. -/
@[expose]
noncomputable def nb095AlphaDummy655 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy625 D R S_cls E)
          (synWrex (nb095AlphaDummy626 D R S_cls E)
            (Class.cv (nb095AlphaDummy620 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy625 D R S_cls E)
          (synWrex (nb095AlphaDummy626 D R S_cls E)
            (Class.cv (nb095AlphaDummy620 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_656`. -/
@[expose]
noncomputable def nb095AlphaDummy656 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy627 x D R)
          (synWrex (nb095AlphaDummy628 x D R) (Class.cv (nb095AlphaDummy622 x D R))
            (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
              (synCun (synCphi (Class.cv (nb095AlphaDummy628 x D R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy627 x D R)
          (synWrex (nb095AlphaDummy628 x D R) (Class.cv (nb095AlphaDummy622 x D R))
            (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
              (synCun (synCphi (Class.cv (nb095AlphaDummy628 x D R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_657`. -/
@[expose]
noncomputable def nb095AlphaDummy657 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_658`. -/
@[expose]
noncomputable def nb095AlphaDummy658 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy628 x D R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_659`. -/
@[expose]
noncomputable def nb095AlphaDummy659 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_660`. -/
@[expose]
noncomputable def nb095AlphaDummy660 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy628 x D R)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy628 x D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_661`. -/
@[expose]
noncomputable def nb095AlphaDummy661 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
          (Class.cv (nb095AlphaDummy003 D R S_cls E)))).fv ∪
      ((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
          (Class.cv (nb095AlphaDummy004 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_662`. -/
@[expose]
noncomputable def nb095AlphaDummy662 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
          (Class.cv (nb095AlphaDummy003 D R S_cls E)))).fv ∪
      ((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
          (Class.cv (nb095AlphaDummy004 D R S_cls E)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_663`. -/
@[expose]
noncomputable def nb095AlphaDummy663 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))).fv ∪
      ((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_664`. -/
@[expose]
noncomputable def nb095AlphaDummy664 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))).fv ∪
      ((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_665`. -/
@[expose]
noncomputable def nb095AlphaDummy665 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy661 D R S_cls E)
            (synWrex (nb095AlphaDummy662 D R S_cls E)
              (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy003 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy661 D R S_cls E)
            (synWrex (nb095AlphaDummy662 D R S_cls E)
              (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy004 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_666`. -/
@[expose]
noncomputable def nb095AlphaDummy666 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))))))).fv ∪
      ((synCcompl (Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_667`. -/
@[expose]
noncomputable def nb095AlphaDummy667 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy661 D R S_cls E)
          (synWrex (nb095AlphaDummy662 D R S_cls E)
            (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
              (Class.cv (nb095AlphaDummy003 D R S_cls E)))
            (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy661 D R S_cls E)
          (synWrex (nb095AlphaDummy662 D R S_cls E)
            (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
              (Class.cv (nb095AlphaDummy003 D R S_cls E)))
            (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_668`. -/
@[expose]
noncomputable def nb095AlphaDummy668 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
          (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
            (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
            (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
              (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
          (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
            (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
            (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
              (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_669`. -/
@[expose]
noncomputable def nb095AlphaDummy669 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_670`. -/
@[expose]
noncomputable def nb095AlphaDummy670 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_671`. -/
@[expose]
noncomputable def nb095AlphaDummy671 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (({(nb095AlphaDummy669 D R S_cls E)} : Finset Var) ∪
      ((synWbr (Class.cv (nb095AlphaDummy003 D R S_cls E))
          (Class.cv (nb095AlphaDummy000 D R S_cls E))
          (Class.cv (nb095AlphaDummy669 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_672`. -/
@[expose]
noncomputable def nb095AlphaDummy672 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (({(nb095AlphaDummy670 x u D R S_cls f E)} : Finset Var) ∪
      ((synWbr (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)) (Class.cv f)
          (Class.cv (nb095AlphaDummy670 x u D R S_cls f E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_673`. -/
@[expose]
noncomputable def nb095AlphaDummy673 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy671 D R S_cls E) (Wff.classEq
          (Class.cab (nb095AlphaDummy669 D R S_cls E)
            (synWbr (Class.cv (nb095AlphaDummy003 D R S_cls E))
              (Class.cv (nb095AlphaDummy000 D R S_cls E))
              (Class.cv (nb095AlphaDummy669 D R S_cls E))))
          (synCsn (Class.cv (nb095AlphaDummy671 D R S_cls E)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_674`. -/
@[expose]
noncomputable def nb095AlphaDummy674 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy671 D R S_cls E) (Wff.classEq
          (Class.cab (nb095AlphaDummy669 D R S_cls E)
            (synWbr (Class.cv (nb095AlphaDummy003 D R S_cls E))
              (Class.cv (nb095AlphaDummy000 D R S_cls E))
              (Class.cv (nb095AlphaDummy669 D R S_cls E))))
          (synCsn (Class.cv (nb095AlphaDummy671 D R S_cls E)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_675`. -/
@[expose]
noncomputable def nb095AlphaDummy675 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy672 x u D R S_cls f E) (Wff.classEq
          (Class.cab (nb095AlphaDummy670 x u D R S_cls f E)
            (synWbr (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)) (Class.cv f)
              (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))))
          (synCsn (Class.cv (nb095AlphaDummy672 x u D R S_cls f E)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_676`. -/
@[expose]
noncomputable def nb095AlphaDummy676 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy672 x u D R S_cls f E) (Wff.classEq
          (Class.cab (nb095AlphaDummy670 x u D R S_cls f E)
            (synWbr (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)) (Class.cv f)
              (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))))
          (synCsn (Class.cv (nb095AlphaDummy672 x u D R S_cls f E)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_677`. -/
@[expose]
noncomputable def nb095AlphaDummy677 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy669 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_678`. -/
@[expose]
noncomputable def nb095AlphaDummy678 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy669 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_679`. -/
@[expose]
noncomputable def nb095AlphaDummy679 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095AlphaDummy670 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_680`. -/
@[expose]
noncomputable def nb095AlphaDummy680 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095AlphaDummy670 x u D R S_cls f E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_681`. -/
@[expose]
noncomputable def nb095AlphaDummy681 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy677 D R S_cls E)
            (synWrex (nb095AlphaDummy678 D R S_cls E)
              (Class.cv (nb095AlphaDummy003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy677 D R S_cls E)
            (synWrex (nb095AlphaDummy678 D R S_cls E)
              (Class.cv (nb095AlphaDummy669 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_682`. -/
@[expose]
noncomputable def nb095AlphaDummy682 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))))))).fv ∪
      ((synCcompl (Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_683`. -/
@[expose]
noncomputable def nb095AlphaDummy683 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy677 D R S_cls E)
          (synWrex (nb095AlphaDummy678 D R S_cls E)
            (Class.cv (nb095AlphaDummy003 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy677 D R S_cls E)
          (synWrex (nb095AlphaDummy678 D R S_cls E)
            (Class.cv (nb095AlphaDummy003 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_684`. -/
@[expose]
noncomputable def nb095AlphaDummy684 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
          (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
            (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
              (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
          (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
            (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
              (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_685`. -/
@[expose]
noncomputable def nb095AlphaDummy685 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy678 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_686`. -/
@[expose]
noncomputable def nb095AlphaDummy686 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy678 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_687`. -/
@[expose]
noncomputable def nb095AlphaDummy687 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy680 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_688`. -/
@[expose]
noncomputable def nb095AlphaDummy688 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy680 x u D R S_cls f E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_689`. -/
@[expose]
noncomputable def nb095AlphaDummy689 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy685 D R S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy685 D R S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy685 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_690`. -/
@[expose]
noncomputable def nb095AlphaDummy690 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar
    (((Wff.classMem (Class.cv (nb095AlphaDummy687 x u D R S_cls f E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy687 x u D R S_cls f E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_691`. -/
@[expose]
noncomputable def nb095AlphaDummy691 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy685 D R S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_692`. -/
@[expose]
noncomputable def nb095AlphaDummy692 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy685 D R S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_693`. -/
@[expose]
noncomputable def nb095AlphaDummy693 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy685 D R S_cls E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_694`. -/
@[expose]
noncomputable def nb095AlphaDummy694 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_695`. -/
@[expose]
noncomputable def nb095AlphaDummy695 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_696`. -/
@[expose]
noncomputable def nb095AlphaDummy696 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_697`. -/
@[expose]
noncomputable def nb095AlphaDummy697 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy692 D R S_cls E))
          (Class.cv (nb095AlphaDummy693 D R S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy692 D R S_cls E))
          (Class.cv (nb095AlphaDummy693 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_698`. -/
@[expose]
noncomputable def nb095AlphaDummy698 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy695 x u D R S_cls f E))
          (Class.cv (nb095AlphaDummy696 x u D R S_cls f E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy695 x u D R S_cls f E))
          (Class.cv (nb095AlphaDummy696 x u D R S_cls f E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_699`. -/
@[expose]
noncomputable def nb095AlphaDummy699 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy692 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy693 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_700`. -/
@[expose]
noncomputable def nb095AlphaDummy700 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy695 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095AlphaDummy696 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_701`. -/
@[expose]
noncomputable def nb095AlphaDummy701 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy692 D R S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy693 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_702`. -/
@[expose]
noncomputable def nb095AlphaDummy702 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy695 x u D R S_cls f E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy696 x u D R S_cls f E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_703`. -/
@[expose]
noncomputable def nb095AlphaDummy703 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy692 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy692 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_704`. -/
@[expose]
noncomputable def nb095AlphaDummy704 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy695 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095AlphaDummy695 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_705`. -/
@[expose]
noncomputable def nb095AlphaDummy705 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy693 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy693 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_706`. -/
@[expose]
noncomputable def nb095AlphaDummy706 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy696 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095AlphaDummy696 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_707`. -/
@[expose]
noncomputable def nb095AlphaDummy707 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy677 D R S_cls E)
          (synWrex (nb095AlphaDummy678 D R S_cls E)
            (Class.cv (nb095AlphaDummy669 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy677 D R S_cls E)
          (synWrex (nb095AlphaDummy678 D R S_cls E)
            (Class.cv (nb095AlphaDummy669 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_708`. -/
@[expose]
noncomputable def nb095AlphaDummy708 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
          (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
            (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))
                (synCsn (synC0c))))))).fv ∪
      ((Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
          (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
            (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_709`. -/
@[expose]
noncomputable def nb095AlphaDummy709 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_710`. -/
@[expose]
noncomputable def nb095AlphaDummy710 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_711`. -/
@[expose]
noncomputable def nb095AlphaDummy711 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_712`. -/
@[expose]
noncomputable def nb095AlphaDummy712 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_713`. -/
@[expose]
noncomputable def nb095AlphaDummy713 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy671 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_714`. -/
@[expose]
noncomputable def nb095AlphaDummy714 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy672 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_715`. -/
@[expose]
noncomputable def nb095AlphaDummy715 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy662 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_716`. -/
@[expose]
noncomputable def nb095AlphaDummy716 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy662 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_717`. -/
@[expose]
noncomputable def nb095AlphaDummy717 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy664 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_718`. -/
@[expose]
noncomputable def nb095AlphaDummy718 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy664 x u D R S_cls f E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_719`. -/
@[expose]
noncomputable def nb095AlphaDummy719 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy715 D R S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy715 D R S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy715 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_720`. -/
@[expose]
noncomputable def nb095AlphaDummy720 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar
    (((Wff.classMem (Class.cv (nb095AlphaDummy717 x u D R S_cls f E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy717 x u D R S_cls f E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_721`. -/
@[expose]
noncomputable def nb095AlphaDummy721 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy715 D R S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_722`. -/
@[expose]
noncomputable def nb095AlphaDummy722 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy715 D R S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_723`. -/
@[expose]
noncomputable def nb095AlphaDummy723 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy715 D R S_cls E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_724`. -/
@[expose]
noncomputable def nb095AlphaDummy724 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_725`. -/
@[expose]
noncomputable def nb095AlphaDummy725 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_726`. -/
@[expose]
noncomputable def nb095AlphaDummy726 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_727`. -/
@[expose]
noncomputable def nb095AlphaDummy727 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy722 D R S_cls E))
          (Class.cv (nb095AlphaDummy723 D R S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy722 D R S_cls E))
          (Class.cv (nb095AlphaDummy723 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_728`. -/
@[expose]
noncomputable def nb095AlphaDummy728 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy725 x u D R S_cls f E))
          (Class.cv (nb095AlphaDummy726 x u D R S_cls f E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy725 x u D R S_cls f E))
          (Class.cv (nb095AlphaDummy726 x u D R S_cls f E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_729`. -/
@[expose]
noncomputable def nb095AlphaDummy729 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy722 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy723 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_730`. -/
@[expose]
noncomputable def nb095AlphaDummy730 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy725 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095AlphaDummy726 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_731`. -/
@[expose]
noncomputable def nb095AlphaDummy731 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy722 D R S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy723 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_732`. -/
@[expose]
noncomputable def nb095AlphaDummy732 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy725 x u D R S_cls f E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy726 x u D R S_cls f E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_733`. -/
@[expose]
noncomputable def nb095AlphaDummy733 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy722 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy722 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_734`. -/
@[expose]
noncomputable def nb095AlphaDummy734 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy725 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095AlphaDummy725 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_735`. -/
@[expose]
noncomputable def nb095AlphaDummy735 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy723 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy723 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_736`. -/
@[expose]
noncomputable def nb095AlphaDummy736 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy726 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095AlphaDummy726 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_737`. -/
@[expose]
noncomputable def nb095AlphaDummy737 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy661 D R S_cls E)
          (synWrex (nb095AlphaDummy662 D R S_cls E)
            (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
              (Class.cv (nb095AlphaDummy004 D R S_cls E)))
            (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy661 D R S_cls E)
          (synWrex (nb095AlphaDummy662 D R S_cls E)
            (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
              (Class.cv (nb095AlphaDummy004 D R S_cls E)))
            (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_738`. -/
@[expose]
noncomputable def nb095AlphaDummy738 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
          (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
            (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))
            (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))
                (synCsn (synC0c))))))).fv ∪
      ((Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
          (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
            (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))
            (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_739`. -/
@[expose]
noncomputable def nb095AlphaDummy739 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_740`. -/
@[expose]
noncomputable def nb095AlphaDummy740 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_741`. -/
@[expose]
noncomputable def nb095AlphaDummy741 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (({(nb095AlphaDummy739 D R S_cls E)} : Finset Var) ∪
      ((synWbr (Class.cv (nb095AlphaDummy004 D R S_cls E))
          (Class.cv (nb095AlphaDummy000 D R S_cls E))
          (Class.cv (nb095AlphaDummy739 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_742`. -/
@[expose]
noncomputable def nb095AlphaDummy742 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (({(nb095AlphaDummy740 x u D R S_cls f E)} : Finset Var) ∪
      ((synWbr (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)) (Class.cv f)
          (Class.cv (nb095AlphaDummy740 x u D R S_cls f E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_743`. -/
@[expose]
noncomputable def nb095AlphaDummy743 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy741 D R S_cls E) (Wff.classEq
          (Class.cab (nb095AlphaDummy739 D R S_cls E)
            (synWbr (Class.cv (nb095AlphaDummy004 D R S_cls E))
              (Class.cv (nb095AlphaDummy000 D R S_cls E))
              (Class.cv (nb095AlphaDummy739 D R S_cls E))))
          (synCsn (Class.cv (nb095AlphaDummy741 D R S_cls E)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_744`. -/
@[expose]
noncomputable def nb095AlphaDummy744 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy741 D R S_cls E) (Wff.classEq
          (Class.cab (nb095AlphaDummy739 D R S_cls E)
            (synWbr (Class.cv (nb095AlphaDummy004 D R S_cls E))
              (Class.cv (nb095AlphaDummy000 D R S_cls E))
              (Class.cv (nb095AlphaDummy739 D R S_cls E))))
          (synCsn (Class.cv (nb095AlphaDummy741 D R S_cls E)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_745`. -/
@[expose]
noncomputable def nb095AlphaDummy745 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy742 x u D R S_cls f E) (Wff.classEq
          (Class.cab (nb095AlphaDummy740 x u D R S_cls f E)
            (synWbr (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)) (Class.cv f)
              (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))))
          (synCsn (Class.cv (nb095AlphaDummy742 x u D R S_cls f E)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_746`. -/
@[expose]
noncomputable def nb095AlphaDummy746 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy742 x u D R S_cls f E) (Wff.classEq
          (Class.cab (nb095AlphaDummy740 x u D R S_cls f E)
            (synWbr (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)) (Class.cv f)
              (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))))
          (synCsn (Class.cv (nb095AlphaDummy742 x u D R S_cls f E)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_747`. -/
@[expose]
noncomputable def nb095AlphaDummy747 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy739 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_748`. -/
@[expose]
noncomputable def nb095AlphaDummy748 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy739 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_749`. -/
@[expose]
noncomputable def nb095AlphaDummy749 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095AlphaDummy740 x u D R S_cls f E))).fv) 0)

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

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_750`. -/
@[expose]
noncomputable def nb095AlphaDummy750 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095AlphaDummy740 x u D R S_cls f E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_751`. -/
@[expose]
noncomputable def nb095AlphaDummy751 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy747 D R S_cls E)
            (synWrex (nb095AlphaDummy748 D R S_cls E)
              (Class.cv (nb095AlphaDummy004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy747 D R S_cls E)
            (synWrex (nb095AlphaDummy748 D R S_cls E)
              (Class.cv (nb095AlphaDummy739 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_752`. -/
@[expose]
noncomputable def nb095AlphaDummy752 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))))))).fv ∪
      ((synCcompl (Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_753`. -/
@[expose]
noncomputable def nb095AlphaDummy753 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy747 D R S_cls E)
          (synWrex (nb095AlphaDummy748 D R S_cls E)
            (Class.cv (nb095AlphaDummy004 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy747 D R S_cls E)
          (synWrex (nb095AlphaDummy748 D R S_cls E)
            (Class.cv (nb095AlphaDummy004 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_754`. -/
@[expose]
noncomputable def nb095AlphaDummy754 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
          (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
            (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
              (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
          (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
            (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
              (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_755`. -/
@[expose]
noncomputable def nb095AlphaDummy755 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy748 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_756`. -/
@[expose]
noncomputable def nb095AlphaDummy756 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy748 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_757`. -/
@[expose]
noncomputable def nb095AlphaDummy757 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy750 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_758`. -/
@[expose]
noncomputable def nb095AlphaDummy758 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy750 x u D R S_cls f E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_759`. -/
@[expose]
noncomputable def nb095AlphaDummy759 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy755 D R S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy755 D R S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_760`. -/
@[expose]
noncomputable def nb095AlphaDummy760 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar
    (((Wff.classMem (Class.cv (nb095AlphaDummy757 x u D R S_cls f E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy757 x u D R S_cls f E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_761`. -/
@[expose]
noncomputable def nb095AlphaDummy761 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_762`. -/
@[expose]
noncomputable def nb095AlphaDummy762 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_763`. -/
@[expose]
noncomputable def nb095AlphaDummy763 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_764`. -/
@[expose]
noncomputable def nb095AlphaDummy764 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_765`. -/
@[expose]
noncomputable def nb095AlphaDummy765 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_766`. -/
@[expose]
noncomputable def nb095AlphaDummy766 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_767`. -/
@[expose]
noncomputable def nb095AlphaDummy767 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy762 D R S_cls E))
          (Class.cv (nb095AlphaDummy763 D R S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy762 D R S_cls E))
          (Class.cv (nb095AlphaDummy763 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_768`. -/
@[expose]
noncomputable def nb095AlphaDummy768 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy765 x u D R S_cls f E))
          (Class.cv (nb095AlphaDummy766 x u D R S_cls f E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy765 x u D R S_cls f E))
          (Class.cv (nb095AlphaDummy766 x u D R S_cls f E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_769`. -/
@[expose]
noncomputable def nb095AlphaDummy769 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy762 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy763 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_770`. -/
@[expose]
noncomputable def nb095AlphaDummy770 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy765 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095AlphaDummy766 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_771`. -/
@[expose]
noncomputable def nb095AlphaDummy771 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy762 D R S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy763 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_772`. -/
@[expose]
noncomputable def nb095AlphaDummy772 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy765 x u D R S_cls f E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy766 x u D R S_cls f E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_773`. -/
@[expose]
noncomputable def nb095AlphaDummy773 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy762 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy762 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_774`. -/
@[expose]
noncomputable def nb095AlphaDummy774 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy765 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095AlphaDummy765 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_775`. -/
@[expose]
noncomputable def nb095AlphaDummy775 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy763 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy763 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_776`. -/
@[expose]
noncomputable def nb095AlphaDummy776 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy766 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095AlphaDummy766 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_777`. -/
@[expose]
noncomputable def nb095AlphaDummy777 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy747 D R S_cls E)
          (synWrex (nb095AlphaDummy748 D R S_cls E)
            (Class.cv (nb095AlphaDummy739 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy747 D R S_cls E)
          (synWrex (nb095AlphaDummy748 D R S_cls E)
            (Class.cv (nb095AlphaDummy739 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_778`. -/
@[expose]
noncomputable def nb095AlphaDummy778 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
          (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
            (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))
                (synCsn (synC0c))))))).fv ∪
      ((Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
          (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
            (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_779`. -/
@[expose]
noncomputable def nb095AlphaDummy779 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_780`. -/
@[expose]
noncomputable def nb095AlphaDummy780 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_781`. -/
@[expose]
noncomputable def nb095AlphaDummy781 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_782`. -/
@[expose]
noncomputable def nb095AlphaDummy782 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_783`. -/
@[expose]
noncomputable def nb095AlphaDummy783 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy741 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_784`. -/
@[expose]
noncomputable def nb095AlphaDummy784 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy742 x u D R S_cls f E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_785`. -/
@[expose]
noncomputable def nb095AlphaDummy785 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_786`. -/
@[expose]
noncomputable def nb095AlphaDummy786 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_787`. -/
@[expose]
noncomputable def nb095AlphaDummy787 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_788`. -/
@[expose]
noncomputable def nb095AlphaDummy788 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_789`. -/
@[expose]
noncomputable def nb095AlphaDummy789 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin S_cls (synCxp (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
      ((synCnin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_790`. -/
@[expose]
noncomputable def nb095AlphaDummy790 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((synCnin S_cls (synCxp (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
            (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv u))))))).fv ∪ ((synCnin S_cls (synCxp (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
            (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv u))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_791`. -/
@[expose]
noncomputable def nb095AlphaDummy791 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar ((S_cls).fv ∪ ((synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_792`. -/
@[expose]
noncomputable def nb095AlphaDummy792 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar ((S_cls).fv ∪ ((synCxp (synCin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))) (synCin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_793`. -/
@[expose]
noncomputable def nb095AlphaDummy793 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv ∪ ((synCin E
          (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_794`. -/
@[expose]
noncomputable def nb095AlphaDummy794 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv ∪ ((synCin E
          (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_795`. -/
@[expose]
noncomputable def nb095AlphaDummy795 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((synCin E
          (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv ∪
      ((synCin E (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_796`. -/
@[expose]
noncomputable def nb095AlphaDummy796 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((synCin E
          (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv ∪
      ((synCin E (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv)
    1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_797`. -/
@[expose]
noncomputable def nb095AlphaDummy797 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (({(nb095AlphaDummy793 D R S_cls E)} : Finset Var) ∪
        ({(nb095AlphaDummy794 D R S_cls E)} : Finset Var) ∪ ((synWa
          (Wff.classMem (Class.cv (nb095AlphaDummy793 D R S_cls E)) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))
          (Wff.classMem (Class.cv (nb095AlphaDummy794 D R S_cls E)) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_798`. -/
@[expose]
noncomputable def nb095AlphaDummy798 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (({(nb095AlphaDummy795 u S_cls E)} : Finset Var) ∪
        ({(nb095AlphaDummy796 u S_cls E)} : Finset Var) ∪ ((synWa
          (Wff.classMem (Class.cv (nb095AlphaDummy795 u S_cls E)) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))
          (Wff.classMem (Class.cv (nb095AlphaDummy796 u S_cls E)) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_799`. -/
@[expose]
noncomputable def nb095AlphaDummy799 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy793 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy794 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_800`. -/
@[expose]
noncomputable def nb095AlphaDummy800 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy793 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy794 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_801`. -/
@[expose]
noncomputable def nb095AlphaDummy801 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy795 u S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy796 u S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_802`. -/
@[expose]
noncomputable def nb095AlphaDummy802 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy795 u S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy796 u S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_803`. -/
@[expose]
noncomputable def nb095AlphaDummy803 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy799 D R S_cls E)
            (synWrex (nb095AlphaDummy800 D R S_cls E)
              (Class.cv (nb095AlphaDummy793 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy799 D R S_cls E)
            (synWrex (nb095AlphaDummy800 D R S_cls E)
              (Class.cv (nb095AlphaDummy794 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_804`. -/
@[expose]
noncomputable def nb095AlphaDummy804 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy801 u S_cls E)
            (synWrex (nb095AlphaDummy802 u S_cls E)
              (Class.cv (nb095AlphaDummy795 u S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy801 u S_cls E)
            (synWrex (nb095AlphaDummy802 u S_cls E)
              (Class.cv (nb095AlphaDummy796 u S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_805`. -/
@[expose]
noncomputable def nb095AlphaDummy805 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy799 D R S_cls E)
          (synWrex (nb095AlphaDummy800 D R S_cls E)
            (Class.cv (nb095AlphaDummy793 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy799 D R S_cls E)
          (synWrex (nb095AlphaDummy800 D R S_cls E)
            (Class.cv (nb095AlphaDummy793 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_806`. -/
@[expose]
noncomputable def nb095AlphaDummy806 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy801 u S_cls E)
          (synWrex (nb095AlphaDummy802 u S_cls E)
            (Class.cv (nb095AlphaDummy795 u S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy801 u S_cls E) (synWrex (nb095AlphaDummy802 u S_cls E)
            (Class.cv (nb095AlphaDummy795 u S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_807`. -/
@[expose]
noncomputable def nb095AlphaDummy807 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy800 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_808`. -/
@[expose]
noncomputable def nb095AlphaDummy808 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy800 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_809`. -/
@[expose]
noncomputable def nb095AlphaDummy809 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy802 u S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_810`. -/
@[expose]
noncomputable def nb095AlphaDummy810 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy802 u S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_811`. -/
@[expose]
noncomputable def nb095AlphaDummy811 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy807 D R S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy807 D R S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_812`. -/
@[expose]
noncomputable def nb095AlphaDummy812 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy809 u S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy809 u S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy809 u S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_813`. -/
@[expose]
noncomputable def nb095AlphaDummy813 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_814`. -/
@[expose]
noncomputable def nb095AlphaDummy814 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_815`. -/
@[expose]
noncomputable def nb095AlphaDummy815 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_816`. -/
@[expose]
noncomputable def nb095AlphaDummy816 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_817`. -/
@[expose]
noncomputable def nb095AlphaDummy817 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_818`. -/
@[expose]
noncomputable def nb095AlphaDummy818 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_819`. -/
@[expose]
noncomputable def nb095AlphaDummy819 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy814 D R S_cls E))
          (Class.cv (nb095AlphaDummy815 D R S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy814 D R S_cls E))
          (Class.cv (nb095AlphaDummy815 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_820`. -/
@[expose]
noncomputable def nb095AlphaDummy820 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy817 u S_cls E))
          (Class.cv (nb095AlphaDummy818 u S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy817 u S_cls E))
          (Class.cv (nb095AlphaDummy818 u S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_821`. -/
@[expose]
noncomputable def nb095AlphaDummy821 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy814 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy815 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_822`. -/
@[expose]
noncomputable def nb095AlphaDummy822 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy817 u S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy818 u S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_823`. -/
@[expose]
noncomputable def nb095AlphaDummy823 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy814 D R S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy815 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_824`. -/
@[expose]
noncomputable def nb095AlphaDummy824 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy817 u S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy818 u S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_825`. -/
@[expose]
noncomputable def nb095AlphaDummy825 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy814 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy814 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_826`. -/
@[expose]
noncomputable def nb095AlphaDummy826 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy817 u S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy817 u S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_827`. -/
@[expose]
noncomputable def nb095AlphaDummy827 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy815 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy815 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_828`. -/
@[expose]
noncomputable def nb095AlphaDummy828 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy818 u S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy818 u S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_829`. -/
@[expose]
noncomputable def nb095AlphaDummy829 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy799 D R S_cls E)
          (synWrex (nb095AlphaDummy800 D R S_cls E)
            (Class.cv (nb095AlphaDummy794 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy799 D R S_cls E)
          (synWrex (nb095AlphaDummy800 D R S_cls E)
            (Class.cv (nb095AlphaDummy794 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_830`. -/
@[expose]
noncomputable def nb095AlphaDummy830 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy801 u S_cls E)
          (synWrex (nb095AlphaDummy802 u S_cls E)
            (Class.cv (nb095AlphaDummy796 u S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy801 u S_cls E)
          (synWrex (nb095AlphaDummy802 u S_cls E)
            (Class.cv (nb095AlphaDummy796 u S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_831`. -/
@[expose]
noncomputable def nb095AlphaDummy831 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_832`. -/
@[expose]
noncomputable def nb095AlphaDummy832 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_833`. -/
@[expose]
noncomputable def nb095AlphaDummy833 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_834`. -/
@[expose]
noncomputable def nb095AlphaDummy834 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))).fv) 0)

theorem nb095_fresh_000 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy025 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy019 D R S_cls E)
            (synWrex (nb095AlphaDummy020 D R S_cls E)
              (Class.cv (nb095AlphaDummy011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy019 D R S_cls E)
            (synWrex (nb095AlphaDummy020 D R S_cls E)
              (Class.cv (nb095AlphaDummy011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy025] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy019 D R S_cls E)
            (synWrex (nb095AlphaDummy020 D R S_cls E)
              (Class.cv (nb095AlphaDummy011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy019 D R S_cls E)
            (synWrex (nb095AlphaDummy020 D R S_cls E)
              (Class.cv (nb095AlphaDummy011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_001 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy049 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy019 D R S_cls E)
            (synWrex (nb095AlphaDummy020 D R S_cls E)
              (Class.cv (nb095AlphaDummy012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy019 D R S_cls E)
            (synWrex (nb095AlphaDummy020 D R S_cls E)
              (Class.cv (nb095AlphaDummy012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy049] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy019 D R S_cls E)
            (synWrex (nb095AlphaDummy020 D R S_cls E)
              (Class.cv (nb095AlphaDummy012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy019 D R S_cls E)
            (synWrex (nb095AlphaDummy020 D R S_cls E)
              (Class.cv (nb095AlphaDummy012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_002 (f : Var) :
    (nb095AlphaDummy026 f) ∉
      (((Class.cab (nb095AlphaDummy021 f)
            (synWrex (nb095AlphaDummy022 f) (Class.cv (nb095AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy021 f))
                (synCphi (Class.cv (nb095AlphaDummy022 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy021 f)
            (synWrex (nb095AlphaDummy022 f) (Class.cv (nb095AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy021 f))
                (synCphi (Class.cv (nb095AlphaDummy022 f))))))).fv) :=
  by
  simpa only [nb095AlphaDummy026] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy021 f)
            (synWrex (nb095AlphaDummy022 f) (Class.cv (nb095AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy021 f))
                (synCphi (Class.cv (nb095AlphaDummy022 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy021 f)
            (synWrex (nb095AlphaDummy022 f) (Class.cv (nb095AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy021 f))
                (synCphi (Class.cv (nb095AlphaDummy022 f))))))).fv)
      0

theorem nb095_fresh_003 (f : Var) :
    (nb095AlphaDummy050 f) ∉
      (((Class.cab (nb095AlphaDummy021 f)
            (synWrex (nb095AlphaDummy022 f) (Class.cv (nb095AlphaDummy015 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy021 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy022 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy021 f)
            (synWrex (nb095AlphaDummy022 f) (Class.cv (nb095AlphaDummy015 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy021 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy022 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy050] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy021 f)
            (synWrex (nb095AlphaDummy022 f) (Class.cv (nb095AlphaDummy015 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy021 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy022 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy021 f)
            (synWrex (nb095AlphaDummy022 f) (Class.cv (nb095AlphaDummy015 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy021 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy022 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_004 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy061 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy055 D R S_cls E)
            (synWrex (nb095AlphaDummy056 D R S_cls E)
              (Class.cv (nb095AlphaDummy011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy055 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy055 D R S_cls E)
            (synWrex (nb095AlphaDummy056 D R S_cls E)
              (Class.cv (nb095AlphaDummy011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy055 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy061] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy055 D R S_cls E)
            (synWrex (nb095AlphaDummy056 D R S_cls E)
              (Class.cv (nb095AlphaDummy011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy055 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy055 D R S_cls E)
            (synWrex (nb095AlphaDummy056 D R S_cls E)
              (Class.cv (nb095AlphaDummy011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy055 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_005 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy085 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy055 D R S_cls E)
            (synWrex (nb095AlphaDummy056 D R S_cls E)
              (Class.cv (nb095AlphaDummy013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy055 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy055 D R S_cls E)
            (synWrex (nb095AlphaDummy056 D R S_cls E)
              (Class.cv (nb095AlphaDummy013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy055 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy085] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy055 D R S_cls E)
            (synWrex (nb095AlphaDummy056 D R S_cls E)
              (Class.cv (nb095AlphaDummy013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy055 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy055 D R S_cls E)
            (synWrex (nb095AlphaDummy056 D R S_cls E)
              (Class.cv (nb095AlphaDummy013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy055 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_006 (f : Var) :
    (nb095AlphaDummy062 f) ∉
      (((Class.cab (nb095AlphaDummy057 f)
            (synWrex (nb095AlphaDummy058 f) (Class.cv (nb095AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy057 f))
                (synCphi (Class.cv (nb095AlphaDummy058 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy057 f)
            (synWrex (nb095AlphaDummy058 f) (Class.cv (nb095AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy057 f))
                (synCphi (Class.cv (nb095AlphaDummy058 f))))))).fv) :=
  by
  simpa only [nb095AlphaDummy062] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy057 f)
            (synWrex (nb095AlphaDummy058 f) (Class.cv (nb095AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy057 f))
                (synCphi (Class.cv (nb095AlphaDummy058 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy057 f)
            (synWrex (nb095AlphaDummy058 f) (Class.cv (nb095AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy057 f))
                (synCphi (Class.cv (nb095AlphaDummy058 f))))))).fv)
      0

theorem nb095_fresh_007 (f : Var) :
    (nb095AlphaDummy086 f) ∉
      (((Class.cab (nb095AlphaDummy057 f)
            (synWrex (nb095AlphaDummy058 f) (Class.cv (nb095AlphaDummy016 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy057 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy058 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy057 f)
            (synWrex (nb095AlphaDummy058 f) (Class.cv (nb095AlphaDummy016 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy057 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy058 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy086] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy057 f)
            (synWrex (nb095AlphaDummy058 f) (Class.cv (nb095AlphaDummy016 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy057 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy058 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy057 f)
            (synWrex (nb095AlphaDummy058 f) (Class.cv (nb095AlphaDummy016 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy057 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy058 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_008 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy103 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy097 D R S_cls E)
            (synWrex (nb095AlphaDummy098 D R S_cls E)
              (Class.cv (nb095AlphaDummy091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy097 D R S_cls E)
            (synWrex (nb095AlphaDummy098 D R S_cls E)
              (Class.cv (nb095AlphaDummy091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy103] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy097 D R S_cls E)
            (synWrex (nb095AlphaDummy098 D R S_cls E)
              (Class.cv (nb095AlphaDummy091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy097 D R S_cls E)
            (synWrex (nb095AlphaDummy098 D R S_cls E)
              (Class.cv (nb095AlphaDummy091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_009 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy127 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy097 D R S_cls E)
            (synWrex (nb095AlphaDummy098 D R S_cls E)
              (Class.cv (nb095AlphaDummy092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy097 D R S_cls E)
            (synWrex (nb095AlphaDummy098 D R S_cls E)
              (Class.cv (nb095AlphaDummy092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy127] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy097 D R S_cls E)
            (synWrex (nb095AlphaDummy098 D R S_cls E)
              (Class.cv (nb095AlphaDummy092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy097 D R S_cls E)
            (synWrex (nb095AlphaDummy098 D R S_cls E)
              (Class.cv (nb095AlphaDummy092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_010 (f : Var) :
    (nb095AlphaDummy104 f) ∉
      (((Class.cab (nb095AlphaDummy099 f)
            (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy093 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                (synCphi (Class.cv (nb095AlphaDummy100 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy099 f)
            (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy093 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                (synCphi (Class.cv (nb095AlphaDummy100 f))))))).fv) :=
  by
  simpa only [nb095AlphaDummy104] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy099 f)
            (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy093 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                (synCphi (Class.cv (nb095AlphaDummy100 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy099 f)
            (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy093 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                (synCphi (Class.cv (nb095AlphaDummy100 f))))))).fv)
      0

theorem nb095_fresh_011 (f : Var) :
    (nb095AlphaDummy128 f) ∉
      (((Class.cab (nb095AlphaDummy099 f)
            (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy094 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy100 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy099 f)
            (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy094 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy100 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy128] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy099 f)
            (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy094 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy100 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy099 f)
            (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy094 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy100 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_012 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy163 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy133 D R S_cls E)
            (synWrex (nb095AlphaDummy134 D R S_cls E)
              (Class.cv (nb095AlphaDummy091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy133 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy133 D R S_cls E)
            (synWrex (nb095AlphaDummy134 D R S_cls E)
              (Class.cv (nb095AlphaDummy091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy133 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy163] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy133 D R S_cls E)
            (synWrex (nb095AlphaDummy134 D R S_cls E)
              (Class.cv (nb095AlphaDummy091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy133 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy133 D R S_cls E)
            (synWrex (nb095AlphaDummy134 D R S_cls E)
              (Class.cv (nb095AlphaDummy091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy133 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_013 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy139 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy133 D R S_cls E)
            (synWrex (nb095AlphaDummy134 D R S_cls E)
              (Class.cv (nb095AlphaDummy092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy133 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy133 D R S_cls E)
            (synWrex (nb095AlphaDummy134 D R S_cls E)
              (Class.cv (nb095AlphaDummy092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy133 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy139] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy133 D R S_cls E)
            (synWrex (nb095AlphaDummy134 D R S_cls E)
              (Class.cv (nb095AlphaDummy092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy133 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy133 D R S_cls E)
            (synWrex (nb095AlphaDummy134 D R S_cls E)
              (Class.cv (nb095AlphaDummy092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy133 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_014 (f : Var) :
    (nb095AlphaDummy164 f) ∉
      (((Class.cab (nb095AlphaDummy135 f)
            (synWrex (nb095AlphaDummy136 f) (Class.cv (nb095AlphaDummy093 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy135 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy136 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy135 f)
            (synWrex (nb095AlphaDummy136 f) (Class.cv (nb095AlphaDummy093 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy135 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy136 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy164] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy135 f)
            (synWrex (nb095AlphaDummy136 f) (Class.cv (nb095AlphaDummy093 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy135 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy136 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy135 f)
            (synWrex (nb095AlphaDummy136 f) (Class.cv (nb095AlphaDummy093 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy135 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy136 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_015 (f : Var) :
    (nb095AlphaDummy140 f) ∉
      (((Class.cab (nb095AlphaDummy135 f)
            (synWrex (nb095AlphaDummy136 f) (Class.cv (nb095AlphaDummy094 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy135 f))
                (synCphi (Class.cv (nb095AlphaDummy136 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy135 f)
            (synWrex (nb095AlphaDummy136 f) (Class.cv (nb095AlphaDummy094 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy135 f))
                (synCphi (Class.cv (nb095AlphaDummy136 f))))))).fv) :=
  by
  simpa only [nb095AlphaDummy140] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy135 f)
            (synWrex (nb095AlphaDummy136 f) (Class.cv (nb095AlphaDummy094 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy135 f))
                (synCphi (Class.cv (nb095AlphaDummy136 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy135 f)
            (synWrex (nb095AlphaDummy136 f) (Class.cv (nb095AlphaDummy094 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy135 f))
                (synCphi (Class.cv (nb095AlphaDummy136 f))))))).fv)
      0

theorem nb095_fresh_016 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy199 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy169 D R S_cls E)
            (synWrex (nb095AlphaDummy170 D R S_cls E)
              (Class.cv (nb095AlphaDummy012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy169 D R S_cls E)
            (synWrex (nb095AlphaDummy170 D R S_cls E)
              (Class.cv (nb095AlphaDummy012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy199] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy169 D R S_cls E)
            (synWrex (nb095AlphaDummy170 D R S_cls E)
              (Class.cv (nb095AlphaDummy012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy169 D R S_cls E)
            (synWrex (nb095AlphaDummy170 D R S_cls E)
              (Class.cv (nb095AlphaDummy012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_017 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy175 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy169 D R S_cls E)
            (synWrex (nb095AlphaDummy170 D R S_cls E)
              (Class.cv (nb095AlphaDummy013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy169 D R S_cls E)
            (synWrex (nb095AlphaDummy170 D R S_cls E)
              (Class.cv (nb095AlphaDummy013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy175] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy169 D R S_cls E)
            (synWrex (nb095AlphaDummy170 D R S_cls E)
              (Class.cv (nb095AlphaDummy013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy169 D R S_cls E)
            (synWrex (nb095AlphaDummy170 D R S_cls E)
              (Class.cv (nb095AlphaDummy013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_018 (f : Var) :
    (nb095AlphaDummy200 f) ∉
      (((Class.cab (nb095AlphaDummy171 f)
            (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy015 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy172 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy171 f)
            (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy015 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy172 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy200] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy171 f)
            (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy015 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy172 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy171 f)
            (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy015 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy172 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_019 (f : Var) :
    (nb095AlphaDummy176 f) ∉
      (((Class.cab (nb095AlphaDummy171 f)
            (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy016 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
                (synCphi (Class.cv (nb095AlphaDummy172 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy171 f)
            (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy016 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
                (synCphi (Class.cv (nb095AlphaDummy172 f))))))).fv) :=
  by
  simpa only [nb095AlphaDummy176] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy171 f)
            (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy016 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
                (synCphi (Class.cv (nb095AlphaDummy172 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy171 f)
            (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy016 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
                (synCphi (Class.cv (nb095AlphaDummy172 f))))))).fv)
      0

theorem nb095_fresh_020 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy239 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy209 D R S_cls E)
            (synWrex (nb095AlphaDummy210 D R S_cls E)
              (Class.cv (nb095AlphaDummy205 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy209 D R S_cls E)
            (synWrex (nb095AlphaDummy210 D R S_cls E)
              (Class.cv (nb095AlphaDummy205 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy239] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy209 D R S_cls E)
            (synWrex (nb095AlphaDummy210 D R S_cls E)
              (Class.cv (nb095AlphaDummy205 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy209 D R S_cls E)
            (synWrex (nb095AlphaDummy210 D R S_cls E)
              (Class.cv (nb095AlphaDummy205 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_021 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy215 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy209 D R S_cls E)
            (synWrex (nb095AlphaDummy210 D R S_cls E)
              (Class.cv (nb095AlphaDummy206 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy209 D R S_cls E)
            (synWrex (nb095AlphaDummy210 D R S_cls E)
              (Class.cv (nb095AlphaDummy206 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy215] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy209 D R S_cls E)
            (synWrex (nb095AlphaDummy210 D R S_cls E)
              (Class.cv (nb095AlphaDummy206 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy209 D R S_cls E)
            (synWrex (nb095AlphaDummy210 D R S_cls E)
              (Class.cv (nb095AlphaDummy206 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_022 (f : Var) :
    (nb095AlphaDummy240 f) ∉
      (((Class.cab (nb095AlphaDummy211 f)
            (synWrex (nb095AlphaDummy212 f) (Class.cv (nb095AlphaDummy207 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy212 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy211 f)
            (synWrex (nb095AlphaDummy212 f) (Class.cv (nb095AlphaDummy207 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy212 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy240] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy211 f)
            (synWrex (nb095AlphaDummy212 f) (Class.cv (nb095AlphaDummy207 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy212 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy211 f)
            (synWrex (nb095AlphaDummy212 f) (Class.cv (nb095AlphaDummy207 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy212 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_023 (f : Var) :
    (nb095AlphaDummy216 f) ∉
      (((Class.cab (nb095AlphaDummy211 f)
            (synWrex (nb095AlphaDummy212 f) (Class.cv (nb095AlphaDummy208 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
                (synCphi (Class.cv (nb095AlphaDummy212 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy211 f)
            (synWrex (nb095AlphaDummy212 f) (Class.cv (nb095AlphaDummy208 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
                (synCphi (Class.cv (nb095AlphaDummy212 f))))))).fv) :=
  by
  simpa only [nb095AlphaDummy216] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy211 f)
            (synWrex (nb095AlphaDummy212 f) (Class.cv (nb095AlphaDummy208 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
                (synCphi (Class.cv (nb095AlphaDummy212 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy211 f)
            (synWrex (nb095AlphaDummy212 f) (Class.cv (nb095AlphaDummy208 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
                (synCphi (Class.cv (nb095AlphaDummy212 f))))))).fv)
      0

theorem nb095_fresh_024 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy285 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy255 D R S_cls E)
            (synWrex (nb095AlphaDummy256 D R S_cls E)
              (Class.cv (nb095AlphaDummy249 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy255 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy255 D R S_cls E)
            (synWrex (nb095AlphaDummy256 D R S_cls E)
              (Class.cv (nb095AlphaDummy249 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy255 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy285] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy255 D R S_cls E)
            (synWrex (nb095AlphaDummy256 D R S_cls E)
              (Class.cv (nb095AlphaDummy249 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy255 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy255 D R S_cls E)
            (synWrex (nb095AlphaDummy256 D R S_cls E)
              (Class.cv (nb095AlphaDummy249 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy255 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_025 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy261 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy255 D R S_cls E)
            (synWrex (nb095AlphaDummy256 D R S_cls E)
              (Class.cv (nb095AlphaDummy250 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy255 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy255 D R S_cls E)
            (synWrex (nb095AlphaDummy256 D R S_cls E)
              (Class.cv (nb095AlphaDummy250 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy255 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy261] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy255 D R S_cls E)
            (synWrex (nb095AlphaDummy256 D R S_cls E)
              (Class.cv (nb095AlphaDummy250 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy255 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy255 D R S_cls E)
            (synWrex (nb095AlphaDummy256 D R S_cls E)
              (Class.cv (nb095AlphaDummy250 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy255 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_026 (x : Var) (R : Class) :
    (nb095AlphaDummy286 x R) ∉
      (((Class.cab (nb095AlphaDummy257 x R)
            (synWrex (nb095AlphaDummy258 x R) (Class.cv (nb095AlphaDummy251 x R))
              (Wff.classEq (Class.cv (nb095AlphaDummy257 x R))
                (synCun (synCphi (Class.cv (nb095AlphaDummy258 x R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy257 x R)
            (synWrex (nb095AlphaDummy258 x R) (Class.cv (nb095AlphaDummy251 x R))
              (Wff.classEq (Class.cv (nb095AlphaDummy257 x R))
                (synCun (synCphi (Class.cv (nb095AlphaDummy258 x R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy286] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy257 x R)
            (synWrex (nb095AlphaDummy258 x R) (Class.cv (nb095AlphaDummy251 x R))
              (Wff.classEq (Class.cv (nb095AlphaDummy257 x R))
                (synCun (synCphi (Class.cv (nb095AlphaDummy258 x R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy257 x R)
            (synWrex (nb095AlphaDummy258 x R) (Class.cv (nb095AlphaDummy251 x R))
              (Wff.classEq (Class.cv (nb095AlphaDummy257 x R))
                (synCun (synCphi (Class.cv (nb095AlphaDummy258 x R)))
                  (synCsn (synC0c))))))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
