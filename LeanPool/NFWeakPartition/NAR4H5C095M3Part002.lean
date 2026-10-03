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

@[expose]
noncomputable def nb095_alpha_dummy_450 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_447 f))
          (Class.cv (nb095_alpha_dummy_448 f)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_447 f)) (Class.cv (nb095_alpha_dummy_448 f)))).fv)
    0)

@[expose]
noncomputable def nb095_alpha_dummy_451 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_444 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_445 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_452 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_447 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_448 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_453 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_444 D R S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_445 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_454 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_447 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_448 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_455 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_444 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_444 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_456 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_447 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_447 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_457 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_445 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_445 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_458 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_448 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_448 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_459 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_429 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_429 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_460 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_431 f)
          (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_390 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_431 f)
          (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_390 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_461 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_462 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_432 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_463 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_464 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_465 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_466 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_467 (f : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_468 (f : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_469 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (({(nb095_alpha_dummy_465 D R S_cls E)} : Finset Var) ∪
        ({(nb095_alpha_dummy_466 D R S_cls E)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
          (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
          (Class.cv (nb095_alpha_dummy_465 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_470 (f : Var) : Var :=
  (freshVar (({(nb095_alpha_dummy_467 f)} : Finset Var) ∪
        ({(nb095_alpha_dummy_468 f)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb095_alpha_dummy_468 f)) (syn_ccnv (Class.cv f))
          (Class.cv (nb095_alpha_dummy_467 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_471 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_472 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_473 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_467 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_468 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_474 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_467 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_468 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_475 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_471 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_471 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_476 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_473 f)
            (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_467 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_473 f)
            (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_468 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_477 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_471 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_471 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_478 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_473 f)
          (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_467 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_474 f))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_473 f)
          (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_467 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_474 f))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_479 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_472 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_480 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_472 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_481 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_474 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_482 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_474 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_483 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_479 D R S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_479 D R S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_479 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_484 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_481 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_481 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_481 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_485 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_479 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_486 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_479 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_487 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_479 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_488 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_489 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_490 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_491 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_486 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_487 D R S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_486 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_487 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_492 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_489 f))
          (Class.cv (nb095_alpha_dummy_490 f)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_489 f)) (Class.cv (nb095_alpha_dummy_490 f)))).fv)
    0)

@[expose]
noncomputable def nb095_alpha_dummy_493 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_486 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_487 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_494 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_489 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_490 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_495 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_486 D R S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_487 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_496 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_489 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_490 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_497 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_486 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_486 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_498 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_489 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_489 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_499 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_487 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_487 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_500 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_490 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_490 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_501 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_471 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_471 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_502 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_473 f)
          (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_468 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_473 f)
          (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_468 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_503 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_504 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_474 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_505 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_506 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_507 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_508 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_509 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_468 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_467 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_510 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_468 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_467 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_511 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_507 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_507 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_512 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_509 f)
            (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_468 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_509 f)
            (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_467 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_513 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_507 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_507 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_514 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_509 f)
          (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_468 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_510 f))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_509 f)
          (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_468 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_510 f))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_515 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_508 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_516 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_508 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_517 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_510 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_518 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_510 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_519 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_515 D R S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_515 D R S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_515 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_520 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_517 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_517 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_517 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_521 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_515 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_522 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_515 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_523 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_515 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_524 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_525 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_526 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_527 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_522 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_523 D R S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_522 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_523 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_528 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_525 f))
          (Class.cv (nb095_alpha_dummy_526 f)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_525 f)) (Class.cv (nb095_alpha_dummy_526 f)))).fv)
    0)

@[expose]
noncomputable def nb095_alpha_dummy_529 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_522 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_523 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_530 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_525 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_526 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_531 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_522 D R S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_523 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_532 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_525 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_526 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_533 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_522 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_522 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_534 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_525 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_525 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_535 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_523 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_523 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_536 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_526 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_526 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_537 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_507 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_507 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_538 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_509 f)
          (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_467 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_509 f)
          (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_467 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_539 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_540 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_510 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_541 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_542 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_543 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_544 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_545 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_390 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_389 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_546 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_390 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_389 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_547 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_543 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_543 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_548 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_545 f)
            (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_390 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_545 f)
            (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_389 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_549 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_543 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_543 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_550 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_545 f)
          (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_390 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_546 f))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_545 f)
          (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_390 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_546 f))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_551 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_544 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_552 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_544 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_553 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_546 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_554 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_546 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_555 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_551 D R S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_551 D R S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_551 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_556 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_553 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_553 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_553 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_557 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_558 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_559 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_560 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_561 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_562 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_563 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_558 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_559 D R S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_558 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_559 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_564 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_561 f))
          (Class.cv (nb095_alpha_dummy_562 f)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_561 f)) (Class.cv (nb095_alpha_dummy_562 f)))).fv)
    0)

@[expose]
noncomputable def nb095_alpha_dummy_565 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_558 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_559 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_566 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_561 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_562 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_567 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_558 D R S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_559 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_568 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_561 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_562 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_569 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_558 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_558 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_570 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_561 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_561 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_571 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_559 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_559 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_572 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_562 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_562 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_573 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_543 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_543 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_574 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_545 f)
          (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_389 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_545 f)
          (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_389 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_575 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_576 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_546 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_577 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_578 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_579 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_580 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_581 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_582 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_583 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_579 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_579 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_584 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))))))).fv ∪
      ((syn_ccompl (Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_585 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_579 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_579 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_586 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
          (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
            (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
          (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
            (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_587 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_580 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_588 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_580 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_589 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_590 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_591 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_587 D R S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_587 D R S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_587 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_592 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar
    (((Wff.classMem (Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_593 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_594 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_595 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_596 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_597 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_598 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_599 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_594 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_595 D R S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_594 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_595 D R S_cls E)))).fv) 0)

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

@[expose]
noncomputable def nb095_alpha_dummy_600 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))
          (Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))
          (Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_601 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_594 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_595 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_602 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_603 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_594 D R S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_595 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_604 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_605 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_594 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_594 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_606 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_607 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_595 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_595 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_608 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_609 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_579 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_579 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_610 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
          (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
            (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))
                (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
          (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
            (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_611 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_612 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_613 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_614 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_615 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪ ((syn_cnin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_616 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cnin R (syn_cxp (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))).fv ∪
      ((syn_cnin R (syn_cxp (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_617 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar ((R).fv ∪ ((syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_618 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ ((syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))))).fv)
    0)

@[expose]
noncomputable def nb095_alpha_dummy_619 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_620 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_621 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪ ((syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_622 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪ ((syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_623 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (({(nb095_alpha_dummy_619 D R S_cls E)} : Finset Var) ∪
        ({(nb095_alpha_dummy_620 D R S_cls E)} : Finset Var) ∪ ((syn_wa
          (Wff.classMem (Class.cv (nb095_alpha_dummy_619 D R S_cls E)) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))
          (Wff.classMem (Class.cv (nb095_alpha_dummy_620 D R S_cls E)) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_624 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (({(nb095_alpha_dummy_621 x D R)} : Finset Var) ∪
        ({(nb095_alpha_dummy_622 x D R)} : Finset Var) ∪ ((syn_wa
          (Wff.classMem (Class.cv (nb095_alpha_dummy_621 x D R)) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))))
          (Wff.classMem (Class.cv (nb095_alpha_dummy_622 x D R)) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_625 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_619 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_620 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_626 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_619 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_620 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_627 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_621 x D R))).fv ∪
      ((Class.cv (nb095_alpha_dummy_622 x D R))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_628 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_621 x D R))).fv ∪
      ((Class.cv (nb095_alpha_dummy_622 x D R))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_629 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_625 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_619 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_625 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_620 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_630 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_627 x D R)
            (syn_wrex (nb095_alpha_dummy_628 x D R) (Class.cv (nb095_alpha_dummy_621 x D R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_627 x D R) (syn_wrex (nb095_alpha_dummy_628 x D R)
              (Class.cv (nb095_alpha_dummy_622 x D R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_631 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_625 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_619 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_625 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_619 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_632 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_627 x D R)
          (syn_wrex (nb095_alpha_dummy_628 x D R) (Class.cv (nb095_alpha_dummy_621 x D R))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
              (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_627 x D R)
          (syn_wrex (nb095_alpha_dummy_628 x D R) (Class.cv (nb095_alpha_dummy_621 x D R))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
              (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_633 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_626 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_634 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_626 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_635 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_628 x D R))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_636 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_628 x D R))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_637 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_633 D R S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_633 D R S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_633 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_638 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_635 x D R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_635 x D R)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_635 x D R))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_639 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_633 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_640 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_633 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_641 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_633 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_642 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_643 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_644 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_645 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_640 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_641 D R S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_640 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_641 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_646 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_643 x D R))
          (Class.cv (nb095_alpha_dummy_644 x D R)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_643 x D R))
          (Class.cv (nb095_alpha_dummy_644 x D R)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_647 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_640 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_641 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_648 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_643 x D R))).fv ∪
      ((Class.cv (nb095_alpha_dummy_644 x D R))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_649 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_640 D R S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_641 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_650 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_643 x D R)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_644 x D R)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_651 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_640 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_640 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_652 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_643 x D R))).fv ∪
      ((Class.cv (nb095_alpha_dummy_643 x D R))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_653 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_641 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_641 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_654 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_644 x D R))).fv ∪
      ((Class.cv (nb095_alpha_dummy_644 x D R))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_655 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_625 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_620 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_625 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_620 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_656 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_627 x D R)
          (syn_wrex (nb095_alpha_dummy_628 x D R) (Class.cv (nb095_alpha_dummy_622 x D R))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_627 x D R)
          (syn_wrex (nb095_alpha_dummy_628 x D R) (Class.cv (nb095_alpha_dummy_622 x D R))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_657 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_658 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_659 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_660 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_661 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))).fv ∪
      ((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_662 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))).fv ∪
      ((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_663 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))).fv ∪
      ((syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_664 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))).fv ∪
      ((syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_665 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_661 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
              (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_661 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
              (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_666 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
              (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))))))).fv ∪
      ((syn_ccompl (Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
              (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_667 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_661 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
            (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
              (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_661 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
            (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
              (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_668 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
          (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
            (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
          (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
            (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_669 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_670 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_671 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (({(nb095_alpha_dummy_669 D R S_cls E)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_669 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_672 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (({(nb095_alpha_dummy_670 x u D R S_cls f E)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)) (Class.cv f)
          (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_673 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_671 D R S_cls E) (Wff.classEq
          (Class.cab (nb095_alpha_dummy_669 D R S_cls E)
            (syn_wbr (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
              (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
              (Class.cv (nb095_alpha_dummy_669 D R S_cls E))))
          (syn_csn (Class.cv (nb095_alpha_dummy_671 D R S_cls E)))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_674 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_671 D R S_cls E) (Wff.classEq
          (Class.cab (nb095_alpha_dummy_669 D R S_cls E)
            (syn_wbr (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
              (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
              (Class.cv (nb095_alpha_dummy_669 D R S_cls E))))
          (syn_csn (Class.cv (nb095_alpha_dummy_671 D R S_cls E)))))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_675 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_672 x u D R S_cls f E) (Wff.classEq
          (Class.cab (nb095_alpha_dummy_670 x u D R S_cls f E)
            (syn_wbr (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)) (Class.cv f)
              (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))))
          (syn_csn (Class.cv (nb095_alpha_dummy_672 x u D R S_cls f E)))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_676 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_672 x u D R S_cls f E) (Wff.classEq
          (Class.cab (nb095_alpha_dummy_670 x u D R S_cls f E)
            (syn_wbr (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)) (Class.cv f)
              (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))))
          (syn_csn (Class.cv (nb095_alpha_dummy_672 x u D R S_cls f E)))))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_677 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_669 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_678 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_669 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_679 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_680 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_681 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_677 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_677 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_669 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_682 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))))))).fv ∪
      ((syn_ccompl (Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_683 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_677 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_677 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_684 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
          (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
            (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
          (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
            (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_685 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_678 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_686 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_678 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_687 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_688 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_689 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_685 D R S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_685 D R S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_685 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_690 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar
    (((Wff.classMem (Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_691 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_685 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_692 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_685 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_693 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_685 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_694 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_695 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_696 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_697 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_692 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_693 D R S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_692 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_693 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_698 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))
          (Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))
          (Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_699 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_692 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_693 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_700 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_701 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_692 D R S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_693 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_702 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_703 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_692 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_692 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_704 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_705 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_693 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_693 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_706 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_707 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_677 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_669 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_677 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_669 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_708 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
          (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
            (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))
                (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
          (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
            (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_709 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_710 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_711 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_712 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_713 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_671 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_714 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_672 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_715 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_662 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_716 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_662 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_717 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_718 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_719 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_715 D R S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_715 D R S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_715 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_720 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar
    (((Wff.classMem (Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_721 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_715 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_722 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_715 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_723 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_715 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_724 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_725 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_726 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_727 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_722 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_723 D R S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_722 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_723 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_728 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))
          (Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))
          (Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_729 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_722 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_723 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_730 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_731 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_722 D R S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_723 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_732 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_733 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_722 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_722 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_734 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_735 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_723 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_723 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_736 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_737 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_661 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
            (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
              (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_661 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
            (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
              (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_738 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
          (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
            (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))
                (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
          (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
            (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_739 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_740 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_741 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (({(nb095_alpha_dummy_739 D R S_cls E)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_739 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_742 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (({(nb095_alpha_dummy_740 x u D R S_cls f E)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)) (Class.cv f)
          (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_743 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_741 D R S_cls E) (Wff.classEq
          (Class.cab (nb095_alpha_dummy_739 D R S_cls E)
            (syn_wbr (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
              (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
              (Class.cv (nb095_alpha_dummy_739 D R S_cls E))))
          (syn_csn (Class.cv (nb095_alpha_dummy_741 D R S_cls E)))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_744 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_741 D R S_cls E) (Wff.classEq
          (Class.cab (nb095_alpha_dummy_739 D R S_cls E)
            (syn_wbr (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
              (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
              (Class.cv (nb095_alpha_dummy_739 D R S_cls E))))
          (syn_csn (Class.cv (nb095_alpha_dummy_741 D R S_cls E)))))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_745 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_742 x u D R S_cls f E) (Wff.classEq
          (Class.cab (nb095_alpha_dummy_740 x u D R S_cls f E)
            (syn_wbr (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)) (Class.cv f)
              (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))))
          (syn_csn (Class.cv (nb095_alpha_dummy_742 x u D R S_cls f E)))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_746 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_742 x u D R S_cls f E) (Wff.classEq
          (Class.cab (nb095_alpha_dummy_740 x u D R S_cls f E)
            (syn_wbr (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)) (Class.cv f)
              (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))))
          (syn_csn (Class.cv (nb095_alpha_dummy_742 x u D R S_cls f E)))))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_747 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_739 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_748 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_739 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_749 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))).fv) 0)

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

@[expose]
noncomputable def nb095_alpha_dummy_750 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_751 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_747 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_747 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_739 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_752 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))))))).fv ∪
      ((syn_ccompl (Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_753 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_747 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_747 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_754 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
          (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
            (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
          (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
            (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_755 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_748 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_756 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_748 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_757 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_758 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_759 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_755 D R S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_755 D R S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_755 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_760 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar
    (((Wff.classMem (Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_761 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_755 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_762 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_755 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_763 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_755 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_764 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_765 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_766 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_767 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_762 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_763 D R S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_762 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_763 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_768 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))
          (Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))
          (Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_769 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_762 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_763 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_770 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_771 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_762 D R S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_763 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_772 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_773 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_762 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_762 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_774 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_775 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_763 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_763 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_776 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_777 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_747 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_739 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_747 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_739 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_778 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
          (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
            (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))
                (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
          (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
            (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_779 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_780 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_781 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_782 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_783 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_741 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_784 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_742 x u D R S_cls f E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_785 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_786 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_787 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_788 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_789 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin S_cls (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
      ((syn_cnin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_790 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((syn_cnin S_cls (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv u))))))).fv ∪ ((syn_cnin S_cls (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv u))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_791 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar ((S_cls).fv ∪ ((syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_792 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar ((S_cls).fv ∪ ((syn_cxp (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_793 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪ ((syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_794 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪ ((syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_795 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv ∪
      ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
    0)

@[expose]
noncomputable def nb095_alpha_dummy_796 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv ∪
      ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
    1)

@[expose]
noncomputable def nb095_alpha_dummy_797 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (({(nb095_alpha_dummy_793 D R S_cls E)} : Finset Var) ∪
        ({(nb095_alpha_dummy_794 D R S_cls E)} : Finset Var) ∪ ((syn_wa
          (Wff.classMem (Class.cv (nb095_alpha_dummy_793 D R S_cls E)) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))
          (Wff.classMem (Class.cv (nb095_alpha_dummy_794 D R S_cls E)) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_798 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (({(nb095_alpha_dummy_795 u S_cls E)} : Finset Var) ∪
        ({(nb095_alpha_dummy_796 u S_cls E)} : Finset Var) ∪ ((syn_wa
          (Wff.classMem (Class.cv (nb095_alpha_dummy_795 u S_cls E)) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))
          (Wff.classMem (Class.cv (nb095_alpha_dummy_796 u S_cls E)) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_799 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_793 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_794 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_800 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_793 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_794 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_801 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_795 u S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_796 u S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_802 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_795 u S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_796 u S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_803 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_799 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_793 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_799 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_794 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_804 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_801 u S_cls E)
            (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
              (Class.cv (nb095_alpha_dummy_795 u S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_801 u S_cls E)
            (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
              (Class.cv (nb095_alpha_dummy_796 u S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_805 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_799 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_793 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_799 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_793 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_806 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_801 u S_cls E)
          (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
            (Class.cv (nb095_alpha_dummy_795 u S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_801 u S_cls E) (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
            (Class.cv (nb095_alpha_dummy_795 u S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_807 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_800 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_808 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_800 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_809 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_802 u S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_810 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_802 u S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_811 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_807 D R S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_807 D R S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_807 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_812 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_809 u S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_809 u S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_813 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_807 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_814 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_807 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_815 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_807 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_816 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_817 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_818 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_819 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_814 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_815 D R S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_814 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_815 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_820 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_817 u S_cls E))
          (Class.cv (nb095_alpha_dummy_818 u S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_817 u S_cls E))
          (Class.cv (nb095_alpha_dummy_818 u S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_821 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_814 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_815 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_822 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_817 u S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_818 u S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_823 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_814 D R S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_815 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_824 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_817 u S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_818 u S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_825 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_814 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_814 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_826 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_817 u S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_817 u S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_827 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_815 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_815 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_828 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_818 u S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_818 u S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_829 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_799 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_794 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_799 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_794 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_830 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_801 u S_cls E)
          (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
            (Class.cv (nb095_alpha_dummy_796 u S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_801 u S_cls E)
          (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
            (Class.cv (nb095_alpha_dummy_796 u S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_831 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_832 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_833 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_834 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))).fv) 0)

theorem nb095_fresh_000 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_025 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_019 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_019 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_025] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_019 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_019 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_001 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_049 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_019 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_019 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_049] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_019 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_019 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_002 (f : Var) :
    (nb095_alpha_dummy_026 f) ∉
      (((Class.cab (nb095_alpha_dummy_021 f)
            (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_022 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_021 f)
            (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_022 f))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_026] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_021 f)
            (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_022 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_021 f)
            (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_022 f))))))).fv)
      0

theorem nb095_fresh_003 (f : Var) :
    (nb095_alpha_dummy_050 f) ∉
      (((Class.cab (nb095_alpha_dummy_021 f)
            (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_015 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_021 f)
            (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_015 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_050] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_021 f)
            (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_015 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_021 f)
            (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_015 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_004 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_061 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_055 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_055 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_061] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_055 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_055 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_005 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_085 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_055 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_055 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_085] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_055 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_055 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_006 (f : Var) :
    (nb095_alpha_dummy_062 f) ∉
      (((Class.cab (nb095_alpha_dummy_057 f)
            (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_058 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_057 f)
            (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_058 f))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_062] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_057 f)
            (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_058 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_057 f)
            (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_058 f))))))).fv)
      0

theorem nb095_fresh_007 (f : Var) :
    (nb095_alpha_dummy_086 f) ∉
      (((Class.cab (nb095_alpha_dummy_057 f)
            (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_016 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_057 f)
            (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_016 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_086] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_057 f)
            (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_016 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_057 f)
            (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_016 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_008 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_103 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_097 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_097 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_103] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_097 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_097 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_009 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_127 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_097 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_097 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_127] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_097 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_097 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_010 (f : Var) :
    (nb095_alpha_dummy_104 f) ∉
      (((Class.cab (nb095_alpha_dummy_099 f)
            (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_093 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_100 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_099 f)
            (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_093 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_100 f))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_104] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_099 f)
            (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_093 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_100 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_099 f)
            (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_093 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_100 f))))))).fv)
      0

theorem nb095_fresh_011 (f : Var) :
    (nb095_alpha_dummy_128 f) ∉
      (((Class.cab (nb095_alpha_dummy_099 f)
            (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_094 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_099 f)
            (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_094 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_128] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_099 f)
            (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_094 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_099 f)
            (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_094 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_012 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_163 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_133 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_133 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_163] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_133 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_133 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_013 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_139 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_133 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_133 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_139] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_133 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_133 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_014 (f : Var) :
    (nb095_alpha_dummy_164 f) ∉
      (((Class.cab (nb095_alpha_dummy_135 f)
            (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_093 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_135 f)
            (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_093 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_164] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_135 f)
            (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_093 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_135 f)
            (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_093 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_015 (f : Var) :
    (nb095_alpha_dummy_140 f) ∉
      (((Class.cab (nb095_alpha_dummy_135 f)
            (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_094 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_136 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_135 f)
            (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_094 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_136 f))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_140] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_135 f)
            (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_094 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_136 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_135 f)
            (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_094 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_136 f))))))).fv)
      0

theorem nb095_fresh_016 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_199 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_169 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_169 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_199] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_169 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_169 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_017 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_175 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_169 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_169 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_175] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_169 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_169 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_018 (f : Var) :
    (nb095_alpha_dummy_200 f) ∉
      (((Class.cab (nb095_alpha_dummy_171 f)
            (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_015 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_171 f)
            (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_015 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_200] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_171 f)
            (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_015 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_171 f)
            (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_015 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_019 (f : Var) :
    (nb095_alpha_dummy_176 f) ∉
      (((Class.cab (nb095_alpha_dummy_171 f)
            (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_016 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_172 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_171 f)
            (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_016 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_172 f))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_176] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_171 f)
            (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_016 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_172 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_171 f)
            (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_016 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_172 f))))))).fv)
      0

theorem nb095_fresh_020 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_239 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_209 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_205 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_209 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_205 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_239] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_209 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_205 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_209 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_205 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_021 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_215 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_209 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_206 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_209 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_206 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_215] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_209 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_206 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_209 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_206 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_022 (f : Var) :
    (nb095_alpha_dummy_240 f) ∉
      (((Class.cab (nb095_alpha_dummy_211 f)
            (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_207 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_211 f)
            (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_207 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_240] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_211 f)
            (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_207 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_211 f)
            (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_207 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_023 (f : Var) :
    (nb095_alpha_dummy_216 f) ∉
      (((Class.cab (nb095_alpha_dummy_211 f)
            (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_208 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_212 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_211 f)
            (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_208 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_212 f))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_216] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_211 f)
            (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_208 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_212 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_211 f)
            (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_208 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_212 f))))))).fv)
      0

theorem nb095_fresh_024 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_285 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_255 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_249 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_255 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_249 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_285] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_255 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_249 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_255 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_249 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_025 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_261 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_255 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_250 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_255 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_250 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_261] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_255 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_250 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_255 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_250 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_026 (x : Var) (R : Class) :
    (nb095_alpha_dummy_286 x R) ∉
      (((Class.cab (nb095_alpha_dummy_257 x R)
            (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_251 x R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_257 x R)
            (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_251 x R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_286] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_257 x R)
            (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_251 x R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_257 x R)
            (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_251 x R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
