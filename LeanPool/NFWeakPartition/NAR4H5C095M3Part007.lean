/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part006

/-! NF weak partition development: NAR4H5C095M3Part007. -/


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

theorem nb095_support_mem_0384 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_339 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_345 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_339 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_345 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_339 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_339 D R S_cls E) ≠ (nb095_alpha_dummy_345 D R S_cls E) from (by
          unfold nb095_alpha_dummy_345;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0380 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_339 D R S_cls E) ≠ (nb095_alpha_dummy_346 D R S_cls E) from (by
            unfold nb095_alpha_dummy_346;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0380 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0385 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_341 u S_cls) ∈
      (((Class.cab (nb095_alpha_dummy_347 u S_cls) (syn_wrex (nb095_alpha_dummy_348 u S_cls)
              (Class.cv (nb095_alpha_dummy_341 u S_cls))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_347 u S_cls)
            (syn_wrex (nb095_alpha_dummy_348 u S_cls) (Class.cv (nb095_alpha_dummy_341 u S_cls))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_347 u S_cls) from (by
          unfold nb095_alpha_dummy_347;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0382 u S_cls) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_348 u S_cls) from (by
            unfold nb095_alpha_dummy_348;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0382 u S_cls) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0386 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_346 D R S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0387 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_348 u S_cls) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0388 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_346 D R S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0389 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_348 u S_cls) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0390 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_385 D R S_cls E) ∈
      (({(nb095_alpha_dummy_385 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_386 D R S_cls E)} : Finset Var) ∪
        ((syn_wex (nb095_alpha_dummy_387 D R S_cls E) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
                (syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))
                (Class.cv (nb095_alpha_dummy_387 D R S_cls E)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
                (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
                (Class.cv (nb095_alpha_dummy_386 D R S_cls E)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0391 (f : Var) :
    (nb095_alpha_dummy_388 f) ∈
      (({(nb095_alpha_dummy_388 f)} : Finset Var) ∪ ({(nb095_alpha_dummy_389 f)} : Finset Var) ∪
        ((syn_wex (nb095_alpha_dummy_390 f) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_388 f))
                (syn_ccnv (syn_ccnv (Class.cv f))) (Class.cv (nb095_alpha_dummy_390 f)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_390 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb095_alpha_dummy_389 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0392 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_386 D R S_cls E) ∈
      (({(nb095_alpha_dummy_385 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_386 D R S_cls E)} : Finset Var) ∪
        ((syn_wex (nb095_alpha_dummy_387 D R S_cls E) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
                (syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))
                (Class.cv (nb095_alpha_dummy_387 D R S_cls E)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
                (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
                (Class.cv (nb095_alpha_dummy_386 D R S_cls E)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0393 (f : Var) :
    (nb095_alpha_dummy_389 f) ∈
      (({(nb095_alpha_dummy_388 f)} : Finset Var) ∪ ({(nb095_alpha_dummy_389 f)} : Finset Var) ∪
        ((syn_wex (nb095_alpha_dummy_390 f) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_388 f))
                (syn_ccnv (syn_ccnv (Class.cv f))) (Class.cv (nb095_alpha_dummy_390 f)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_390 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb095_alpha_dummy_389 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0394 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_385 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0395 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_385 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_393 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_393 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_385 D R S_cls E) ≠ (nb095_alpha_dummy_393 D R S_cls E) from (by
          unfold nb095_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0394 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_385 D R S_cls E) ≠ (nb095_alpha_dummy_394 D R S_cls E) from (by
            unfold nb095_alpha_dummy_394;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0394 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0396 (f : Var) :
    (nb095_alpha_dummy_388 f) ∈
      (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_389 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0397 (f : Var) :
    (nb095_alpha_dummy_388 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_395 f)
              (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_388 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_395 f)
              (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_389 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_395 f) from (by
          unfold nb095_alpha_dummy_395;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0396 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_396 f) from (by
            unfold nb095_alpha_dummy_396;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0396 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0398 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_385 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_393 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_393 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_385 D R S_cls E) ≠ (nb095_alpha_dummy_393 D R S_cls E) from (by
          unfold nb095_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0394 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_385 D R S_cls E) ≠ (nb095_alpha_dummy_394 D R S_cls E) from (by
            unfold nb095_alpha_dummy_394;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0394 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0399 (f : Var) :
    (nb095_alpha_dummy_388 f) ∈
      (((Class.cab (nb095_alpha_dummy_395 f)
            (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_388 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_396 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_395 f)
            (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_388 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_396 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_395 f) from (by
          unfold nb095_alpha_dummy_395;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0396 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_396 f) from (by
            unfold nb095_alpha_dummy_396;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0396 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0400 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_394 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_394 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0401 (f : Var) :
    (nb095_alpha_dummy_396 f) ∈ (((Class.cv (nb095_alpha_dummy_396 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0402 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_401 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_401 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_401 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_401 D R S_cls E))).fv) :=
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

theorem nb095_support_mem_0403 (f : Var) :
    (nb095_alpha_dummy_403 f) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_403 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_403 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_403 f))).fv) :=
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

theorem nb095_support_mem_0404 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_401 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_401 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0405 (f : Var) :
    (nb095_alpha_dummy_403 f) ∈
      (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0406 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_408 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_408 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_409 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_408 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_409 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0407 (f : Var) :
    (nb095_alpha_dummy_411 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_411 f))
            (Class.cv (nb095_alpha_dummy_412 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_411 f))
            (Class.cv (nb095_alpha_dummy_412 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0408 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_408 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_408 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_409 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0409 (f : Var) :
    (nb095_alpha_dummy_411 f) ∈
      (((Class.cv (nb095_alpha_dummy_411 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_412 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0410 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_409 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_408 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_409 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_408 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_409 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0411 (f : Var) :
    (nb095_alpha_dummy_412 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_411 f))
            (Class.cv (nb095_alpha_dummy_412 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_411 f))
            (Class.cv (nb095_alpha_dummy_412 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0412 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_409 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_408 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_409 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0413 (f : Var) :
    (nb095_alpha_dummy_412 f) ∈
      (((Class.cv (nb095_alpha_dummy_411 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_412 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0414 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_408 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_408 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_409 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0415 (f : Var) :
    (nb095_alpha_dummy_411 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_411 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_412 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0416 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_408 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_408 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_408 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0417 (f : Var) :
    (nb095_alpha_dummy_411 f) ∈
      (((Class.cv (nb095_alpha_dummy_411 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_411 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0418 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_409 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_408 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_409 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0419 (f : Var) :
    (nb095_alpha_dummy_412 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_411 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_412 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0420 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_409 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_409 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_409 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0421 (f : Var) :
    (nb095_alpha_dummy_412 f) ∈
      (((Class.cv (nb095_alpha_dummy_412 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_412 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0422 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_386 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0423 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_386 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_393 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_393 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_386 D R S_cls E) ≠ (nb095_alpha_dummy_393 D R S_cls E) from (by
          unfold nb095_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0422 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_386 D R S_cls E) ≠ (nb095_alpha_dummy_394 D R S_cls E) from (by
            unfold nb095_alpha_dummy_394;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0422 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0424 (f : Var) :
    (nb095_alpha_dummy_389 f) ∈
      (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_389 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0425 (f : Var) :
    (nb095_alpha_dummy_389 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_395 f)
              (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_388 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_395 f)
              (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_389 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_395 f) from (by
          unfold nb095_alpha_dummy_395;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0424 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_396 f) from (by
            unfold nb095_alpha_dummy_396;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0424 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0426 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_386 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_393 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_393 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_386 D R S_cls E) ≠ (nb095_alpha_dummy_393 D R S_cls E) from (by
          unfold nb095_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0422 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_386 D R S_cls E) ≠ (nb095_alpha_dummy_394 D R S_cls E) from (by
            unfold nb095_alpha_dummy_394;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0422 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0427 (f : Var) :
    (nb095_alpha_dummy_389 f) ∈
      (((Class.cab (nb095_alpha_dummy_395 f)
            (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_389 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_395 f)
            (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_389 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_395 f) from (by
          unfold nb095_alpha_dummy_395;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0424 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_396 f) from (by
            unfold nb095_alpha_dummy_396;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0424 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0428 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_394 D R S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0429 (f : Var) :
    (nb095_alpha_dummy_396 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_396 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0430 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_394 D R S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0431 (f : Var) :
    (nb095_alpha_dummy_396 f) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0432 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_385 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0433 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_385 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_429 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_429 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_385 D R S_cls E) ≠ (nb095_alpha_dummy_429 D R S_cls E) from (by
          unfold nb095_alpha_dummy_429;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0432 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_385 D R S_cls E) ≠ (nb095_alpha_dummy_430 D R S_cls E) from (by
            unfold nb095_alpha_dummy_430;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0432 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0434 (f : Var) :
    (nb095_alpha_dummy_388 f) ∈
      (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_390 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0435 (f : Var) :
    (nb095_alpha_dummy_388 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_431 f)
              (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_388 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_431 f)
              (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_390 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_431 f) from (by
          unfold nb095_alpha_dummy_431;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0434 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_432 f) from (by
            unfold nb095_alpha_dummy_432;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0434 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0436 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_385 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_429 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_429 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_385 D R S_cls E) ≠ (nb095_alpha_dummy_429 D R S_cls E) from (by
          unfold nb095_alpha_dummy_429;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0432 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_385 D R S_cls E) ≠ (nb095_alpha_dummy_430 D R S_cls E) from (by
            unfold nb095_alpha_dummy_430;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0432 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0437 (f : Var) :
    (nb095_alpha_dummy_388 f) ∈
      (((Class.cab (nb095_alpha_dummy_431 f)
            (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_388 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_432 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_431 f)
            (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_388 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_432 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_431 f) from (by
          unfold nb095_alpha_dummy_431;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0434 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_432 f) from (by
            unfold nb095_alpha_dummy_432;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0434 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0438 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_430 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_430 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0439 (f : Var) :
    (nb095_alpha_dummy_432 f) ∈ (((Class.cv (nb095_alpha_dummy_432 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0440 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_437 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_437 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_437 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_437 D R S_cls E))).fv) :=
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

theorem nb095_support_mem_0441 (f : Var) :
    (nb095_alpha_dummy_439 f) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_439 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_439 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_439 f))).fv) :=
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

theorem nb095_support_mem_0442 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_437 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_437 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0443 (f : Var) :
    (nb095_alpha_dummy_439 f) ∈
      (((Class.cv (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0444 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_444 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_444 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_445 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_444 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_445 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0445 (f : Var) :
    (nb095_alpha_dummy_447 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_447 f))
            (Class.cv (nb095_alpha_dummy_448 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_447 f))
            (Class.cv (nb095_alpha_dummy_448 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0446 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_444 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_444 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_445 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0447 (f : Var) :
    (nb095_alpha_dummy_447 f) ∈
      (((Class.cv (nb095_alpha_dummy_447 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_448 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0448 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_445 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_444 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_445 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_444 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_445 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0449 (f : Var) :
    (nb095_alpha_dummy_448 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_447 f))
            (Class.cv (nb095_alpha_dummy_448 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_447 f))
            (Class.cv (nb095_alpha_dummy_448 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0450 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_445 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_444 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_445 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0451 (f : Var) :
    (nb095_alpha_dummy_448 f) ∈
      (((Class.cv (nb095_alpha_dummy_447 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_448 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0452 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_444 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_444 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_445 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0453 (f : Var) :
    (nb095_alpha_dummy_447 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_447 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_448 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0454 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_444 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_444 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_444 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0455 (f : Var) :
    (nb095_alpha_dummy_447 f) ∈
      (((Class.cv (nb095_alpha_dummy_447 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_447 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0456 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_445 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_444 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_445 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0457 (f : Var) :
    (nb095_alpha_dummy_448 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_447 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_448 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0458 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_445 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_445 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_445 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0459 (f : Var) :
    (nb095_alpha_dummy_448 f) ∈
      (((Class.cv (nb095_alpha_dummy_448 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_448 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0460 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_387 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0461 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_387 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_429 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_429 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_387 D R S_cls E) ≠ (nb095_alpha_dummy_429 D R S_cls E) from (by
          unfold nb095_alpha_dummy_429;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0460 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_387 D R S_cls E) ≠ (nb095_alpha_dummy_430 D R S_cls E) from (by
            unfold nb095_alpha_dummy_430;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0460 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0462 (f : Var) :
    (nb095_alpha_dummy_390 f) ∈
      (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_390 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0463 (f : Var) :
    (nb095_alpha_dummy_390 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_431 f)
              (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_388 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_431 f)
              (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_390 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_431 f) from (by
          unfold nb095_alpha_dummy_431;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0462 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_432 f) from (by
            unfold nb095_alpha_dummy_432;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0462 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0464 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_387 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_429 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_429 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_387 D R S_cls E) ≠ (nb095_alpha_dummy_429 D R S_cls E) from (by
          unfold nb095_alpha_dummy_429;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0460 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_387 D R S_cls E) ≠ (nb095_alpha_dummy_430 D R S_cls E) from (by
            unfold nb095_alpha_dummy_430;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0460 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0465 (f : Var) :
    (nb095_alpha_dummy_390 f) ∈
      (((Class.cab (nb095_alpha_dummy_431 f)
            (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_390 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_431 f)
            (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_390 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_431 f) from (by
          unfold nb095_alpha_dummy_431;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0462 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_432 f) from (by
            unfold nb095_alpha_dummy_432;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0462 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0466 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_430 D R S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0467 (f : Var) :
    (nb095_alpha_dummy_432 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_432 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0468 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_430 D R S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0469 (f : Var) :
    (nb095_alpha_dummy_432 f) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0470 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_465 D R S_cls E) ∈
      (({(nb095_alpha_dummy_465 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_466 D R S_cls E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
            (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
            (Class.cv (nb095_alpha_dummy_465 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0471 (f : Var) :
    (nb095_alpha_dummy_467 f) ∈
      (({(nb095_alpha_dummy_467 f)} : Finset Var) ∪ ({(nb095_alpha_dummy_468 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_468 f)) (syn_ccnv (Class.cv f))
            (Class.cv (nb095_alpha_dummy_467 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0472 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_466 D R S_cls E) ∈
      (({(nb095_alpha_dummy_465 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_466 D R S_cls E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
            (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
            (Class.cv (nb095_alpha_dummy_465 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0473 (f : Var) :
    (nb095_alpha_dummy_468 f) ∈
      (({(nb095_alpha_dummy_467 f)} : Finset Var) ∪ ({(nb095_alpha_dummy_468 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_468 f)) (syn_ccnv (Class.cv f))
            (Class.cv (nb095_alpha_dummy_467 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0474 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_465 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0475 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_465 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_471 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_471 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_465 D R S_cls E) ≠ (nb095_alpha_dummy_471 D R S_cls E) from (by
          unfold nb095_alpha_dummy_471;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0474 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_465 D R S_cls E) ≠ (nb095_alpha_dummy_472 D R S_cls E) from (by
            unfold nb095_alpha_dummy_472;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0474 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0476 (f : Var) :
    (nb095_alpha_dummy_467 f) ∈
      (((Class.cv (nb095_alpha_dummy_467 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_468 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0477 (f : Var) :
    (nb095_alpha_dummy_467 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_473 f)
              (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_467 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_473 f)
              (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_468 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_473 f) from (by
          unfold nb095_alpha_dummy_473;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0476 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_474 f) from (by
            unfold nb095_alpha_dummy_474;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0476 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0478 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_465 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_471 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_471 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_465 D R S_cls E) ≠ (nb095_alpha_dummy_471 D R S_cls E) from (by
          unfold nb095_alpha_dummy_471;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0474 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_465 D R S_cls E) ≠ (nb095_alpha_dummy_472 D R S_cls E) from (by
            unfold nb095_alpha_dummy_472;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0474 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0479 (f : Var) :
    (nb095_alpha_dummy_467 f) ∈
      (((Class.cab (nb095_alpha_dummy_473 f)
            (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_467 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_474 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_473 f)
            (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_467 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_474 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_473 f) from (by
          unfold nb095_alpha_dummy_473;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0476 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_474 f) from (by
            unfold nb095_alpha_dummy_474;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0476 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0480 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_472 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_472 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0481 (f : Var) :
    (nb095_alpha_dummy_474 f) ∈ (((Class.cv (nb095_alpha_dummy_474 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0482 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_479 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_479 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_479 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_479 D R S_cls E))).fv) :=
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

theorem nb095_support_mem_0483 (f : Var) :
    (nb095_alpha_dummy_481 f) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_481 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_481 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_481 f))).fv) :=
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

theorem nb095_support_mem_0484 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_479 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_479 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0485 (f : Var) :
    (nb095_alpha_dummy_481 f) ∈
      (((Class.cv (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0486 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_486 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_486 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_487 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_486 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_487 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0487 (f : Var) :
    (nb095_alpha_dummy_489 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_489 f))
            (Class.cv (nb095_alpha_dummy_490 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_489 f))
            (Class.cv (nb095_alpha_dummy_490 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0488 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_486 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_486 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_487 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0489 (f : Var) :
    (nb095_alpha_dummy_489 f) ∈
      (((Class.cv (nb095_alpha_dummy_489 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_490 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0490 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_487 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_486 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_487 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_486 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_487 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0491 (f : Var) :
    (nb095_alpha_dummy_490 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_489 f))
            (Class.cv (nb095_alpha_dummy_490 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_489 f))
            (Class.cv (nb095_alpha_dummy_490 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0492 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_487 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_486 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_487 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0493 (f : Var) :
    (nb095_alpha_dummy_490 f) ∈
      (((Class.cv (nb095_alpha_dummy_489 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_490 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0494 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_486 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_486 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_487 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0495 (f : Var) :
    (nb095_alpha_dummy_489 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_489 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_490 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0496 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_486 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_486 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_486 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0497 (f : Var) :
    (nb095_alpha_dummy_489 f) ∈
      (((Class.cv (nb095_alpha_dummy_489 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_489 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0498 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_487 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_486 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_487 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0499 (f : Var) :
    (nb095_alpha_dummy_490 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_489 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_490 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0500 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_487 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_487 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_487 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0501 (f : Var) :
    (nb095_alpha_dummy_490 f) ∈
      (((Class.cv (nb095_alpha_dummy_490 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_490 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0502 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_466 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0503 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_466 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_471 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_471 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_466 D R S_cls E) ≠ (nb095_alpha_dummy_471 D R S_cls E) from (by
          unfold nb095_alpha_dummy_471;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0502 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_466 D R S_cls E) ≠ (nb095_alpha_dummy_472 D R S_cls E) from (by
            unfold nb095_alpha_dummy_472;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0502 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0504 (f : Var) :
    (nb095_alpha_dummy_468 f) ∈
      (((Class.cv (nb095_alpha_dummy_467 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_468 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0505 (f : Var) :
    (nb095_alpha_dummy_468 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_473 f)
              (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_467 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_473 f)
              (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_468 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_473 f) from (by
          unfold nb095_alpha_dummy_473;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0504 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_474 f) from (by
            unfold nb095_alpha_dummy_474;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0504 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

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

theorem nb095_support_mem_0506 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_466 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_471 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_471 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_466 D R S_cls E) ≠ (nb095_alpha_dummy_471 D R S_cls E) from (by
          unfold nb095_alpha_dummy_471;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0502 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_466 D R S_cls E) ≠ (nb095_alpha_dummy_472 D R S_cls E) from (by
            unfold nb095_alpha_dummy_472;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0502 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0507 (f : Var) :
    (nb095_alpha_dummy_468 f) ∈
      (((Class.cab (nb095_alpha_dummy_473 f)
            (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_468 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_473 f)
            (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_468 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_473 f) from (by
          unfold nb095_alpha_dummy_473;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0504 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_474 f) from (by
            unfold nb095_alpha_dummy_474;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0504 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0508 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_472 D R S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0509 (f : Var) :
    (nb095_alpha_dummy_474 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_474 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0510 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_472 D R S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0511 (f : Var) :
    (nb095_alpha_dummy_474 f) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0512 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_466 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0513 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_466 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_507 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_507 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_466 D R S_cls E) ≠ (nb095_alpha_dummy_507 D R S_cls E) from (by
          unfold nb095_alpha_dummy_507;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0512 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_466 D R S_cls E) ≠ (nb095_alpha_dummy_508 D R S_cls E) from (by
            unfold nb095_alpha_dummy_508;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0512 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0514 (f : Var) :
    (nb095_alpha_dummy_468 f) ∈
      (((Class.cv (nb095_alpha_dummy_468 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_467 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0515 (f : Var) :
    (nb095_alpha_dummy_468 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_509 f)
              (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_468 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_509 f)
              (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_467 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_509 f) from (by
          unfold nb095_alpha_dummy_509;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0514 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_510 f) from (by
            unfold nb095_alpha_dummy_510;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0514 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0516 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_466 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_507 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_507 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_466 D R S_cls E) ≠ (nb095_alpha_dummy_507 D R S_cls E) from (by
          unfold nb095_alpha_dummy_507;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0512 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_466 D R S_cls E) ≠ (nb095_alpha_dummy_508 D R S_cls E) from (by
            unfold nb095_alpha_dummy_508;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0512 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0517 (f : Var) :
    (nb095_alpha_dummy_468 f) ∈
      (((Class.cab (nb095_alpha_dummy_509 f)
            (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_468 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_510 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_509 f)
            (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_468 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_510 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_509 f) from (by
          unfold nb095_alpha_dummy_509;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0514 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_510 f) from (by
            unfold nb095_alpha_dummy_510;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0514 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0518 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_508 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_508 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0519 (f : Var) :
    (nb095_alpha_dummy_510 f) ∈ (((Class.cv (nb095_alpha_dummy_510 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0520 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_515 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_515 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_515 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_515 D R S_cls E))).fv) :=
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

theorem nb095_support_mem_0521 (f : Var) :
    (nb095_alpha_dummy_517 f) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_517 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_517 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_517 f))).fv) :=
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

theorem nb095_support_mem_0522 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_515 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_515 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0523 (f : Var) :
    (nb095_alpha_dummy_517 f) ∈
      (((Class.cv (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0524 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_522 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_522 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_523 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_522 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_523 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0525 (f : Var) :
    (nb095_alpha_dummy_525 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_525 f))
            (Class.cv (nb095_alpha_dummy_526 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_525 f))
            (Class.cv (nb095_alpha_dummy_526 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0526 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_522 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_522 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_523 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0527 (f : Var) :
    (nb095_alpha_dummy_525 f) ∈
      (((Class.cv (nb095_alpha_dummy_525 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_526 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0528 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_523 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_522 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_523 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_522 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_523 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0529 (f : Var) :
    (nb095_alpha_dummy_526 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_525 f))
            (Class.cv (nb095_alpha_dummy_526 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_525 f))
            (Class.cv (nb095_alpha_dummy_526 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0530 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_523 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_522 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_523 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0531 (f : Var) :
    (nb095_alpha_dummy_526 f) ∈
      (((Class.cv (nb095_alpha_dummy_525 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_526 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0532 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_522 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_522 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_523 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0533 (f : Var) :
    (nb095_alpha_dummy_525 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_525 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_526 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0534 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_522 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_522 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_522 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0535 (f : Var) :
    (nb095_alpha_dummy_525 f) ∈
      (((Class.cv (nb095_alpha_dummy_525 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_525 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0536 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_523 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_522 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_523 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0537 (f : Var) :
    (nb095_alpha_dummy_526 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_525 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_526 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0538 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_523 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_523 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_523 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0539 (f : Var) :
    (nb095_alpha_dummy_526 f) ∈
      (((Class.cv (nb095_alpha_dummy_526 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_526 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0540 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_465 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0541 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_465 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_507 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_507 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_465 D R S_cls E) ≠ (nb095_alpha_dummy_507 D R S_cls E) from (by
          unfold nb095_alpha_dummy_507;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0540 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_465 D R S_cls E) ≠ (nb095_alpha_dummy_508 D R S_cls E) from (by
            unfold nb095_alpha_dummy_508;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0540 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0542 (f : Var) :
    (nb095_alpha_dummy_467 f) ∈
      (((Class.cv (nb095_alpha_dummy_468 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_467 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0543 (f : Var) :
    (nb095_alpha_dummy_467 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_509 f)
              (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_468 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_509 f)
              (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_467 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_509 f) from (by
          unfold nb095_alpha_dummy_509;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0542 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_510 f) from (by
            unfold nb095_alpha_dummy_510;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0542 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0544 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_465 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_507 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_507 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_465 D R S_cls E) ≠ (nb095_alpha_dummy_507 D R S_cls E) from (by
          unfold nb095_alpha_dummy_507;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0540 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_465 D R S_cls E) ≠ (nb095_alpha_dummy_508 D R S_cls E) from (by
            unfold nb095_alpha_dummy_508;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0540 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0545 (f : Var) :
    (nb095_alpha_dummy_467 f) ∈
      (((Class.cab (nb095_alpha_dummy_509 f)
            (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_467 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_509 f)
            (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_467 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_509 f) from (by
          unfold nb095_alpha_dummy_509;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0542 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_510 f) from (by
            unfold nb095_alpha_dummy_510;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0542 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0546 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_508 D R S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0547 (f : Var) :
    (nb095_alpha_dummy_510 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_510 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0548 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_508 D R S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0549 (f : Var) :
    (nb095_alpha_dummy_510 f) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0550 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
              (syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))))
            (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
              (syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))))
            (syn_cid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0551 (f : Var) :
    f ∈
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))
            (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))
            (syn_cid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0552 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((syn_ccom (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
            (syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))))).fv ∪
        ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0553 (f : Var) :
    f ∈
      (((syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))).fv ∪
        ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0554 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0555 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (({(nb095_alpha_dummy_385 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_386 D R S_cls E)} : Finset Var) ∪
        ((syn_wex (nb095_alpha_dummy_387 D R S_cls E) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
                (syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))
                (Class.cv (nb095_alpha_dummy_387 D R S_cls E)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
                (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
                (Class.cv (nb095_alpha_dummy_386 D R S_cls E)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_387 D R S_cls E) from (by
          unfold nb095_alpha_dummy_387;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0554 D R S_cls E) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb095_support_mem_0556 (f : Var) :
    f ∈ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0557 (f : Var) :
    f ∈
      (({(nb095_alpha_dummy_388 f)} : Finset Var) ∪ ({(nb095_alpha_dummy_389 f)} : Finset Var) ∪
        ((syn_wex (nb095_alpha_dummy_390 f) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_388 f))
                (syn_ccnv (syn_ccnv (Class.cv f))) (Class.cv (nb095_alpha_dummy_390 f)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_390 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb095_alpha_dummy_389 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show f ≠ (nb095_alpha_dummy_390 f) from (by
          unfold nb095_alpha_dummy_390;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0556 f) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb095_support_mem_0558 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (({(nb095_alpha_dummy_465 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_466 D R S_cls E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
            (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
            (Class.cv (nb095_alpha_dummy_465 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0559 (f : Var) :
    f ∈
      (({(nb095_alpha_dummy_467 f)} : Finset Var) ∪ ({(nb095_alpha_dummy_468 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_468 f)) (syn_ccnv (Class.cv f))
            (Class.cv (nb095_alpha_dummy_467 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0560 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv) :=
  by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0561 (f : Var) : f ∈ (((syn_ccnv (Class.cv f))).fv) :=
  by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0562 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_387 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0563 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_387 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_543 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_543 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_387 D R S_cls E) ≠ (nb095_alpha_dummy_543 D R S_cls E) from (by
          unfold nb095_alpha_dummy_543;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_387 D R S_cls E) ≠ (nb095_alpha_dummy_544 D R S_cls E) from (by
            unfold nb095_alpha_dummy_544;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0564 (f : Var) :
    (nb095_alpha_dummy_390 f) ∈
      (((Class.cv (nb095_alpha_dummy_390 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_389 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0565 (f : Var) :
    (nb095_alpha_dummy_390 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_545 f)
              (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_390 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_545 f)
              (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_389 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_545 f) from (by
          unfold nb095_alpha_dummy_545;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0564 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_546 f) from (by
            unfold nb095_alpha_dummy_546;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0564 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0566 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_387 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_543 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_543 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_387 D R S_cls E) ≠ (nb095_alpha_dummy_543 D R S_cls E) from (by
          unfold nb095_alpha_dummy_543;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_387 D R S_cls E) ≠ (nb095_alpha_dummy_544 D R S_cls E) from (by
            unfold nb095_alpha_dummy_544;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0567 (f : Var) :
    (nb095_alpha_dummy_390 f) ∈
      (((Class.cab (nb095_alpha_dummy_545 f)
            (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_390 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_546 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_545 f)
            (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_390 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_546 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_545 f) from (by
          unfold nb095_alpha_dummy_545;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0564 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_546 f) from (by
            unfold nb095_alpha_dummy_546;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0564 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0568 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_544 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_544 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0569 (f : Var) :
    (nb095_alpha_dummy_546 f) ∈ (((Class.cv (nb095_alpha_dummy_546 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0570 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_551 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_551 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_551 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_551 D R S_cls E))).fv) :=
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

theorem nb095_support_mem_0571 (f : Var) :
    (nb095_alpha_dummy_553 f) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_553 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_553 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_553 f))).fv) :=
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

theorem nb095_support_mem_0572 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_551 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0573 (f : Var) :
    (nb095_alpha_dummy_553 f) ∈
      (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0574 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_558 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_558 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_559 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_558 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_559 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0575 (f : Var) :
    (nb095_alpha_dummy_561 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_561 f))
            (Class.cv (nb095_alpha_dummy_562 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_561 f))
            (Class.cv (nb095_alpha_dummy_562 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0576 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_558 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_558 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_559 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0577 (f : Var) :
    (nb095_alpha_dummy_561 f) ∈
      (((Class.cv (nb095_alpha_dummy_561 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_562 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0578 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_559 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_558 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_559 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_558 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_559 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0579 (f : Var) :
    (nb095_alpha_dummy_562 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_561 f))
            (Class.cv (nb095_alpha_dummy_562 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_561 f))
            (Class.cv (nb095_alpha_dummy_562 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0580 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_559 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_558 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_559 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0581 (f : Var) :
    (nb095_alpha_dummy_562 f) ∈
      (((Class.cv (nb095_alpha_dummy_561 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_562 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0582 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_558 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_558 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_559 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0583 (f : Var) :
    (nb095_alpha_dummy_561 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_561 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_562 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0584 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_558 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_558 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_558 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0585 (f : Var) :
    (nb095_alpha_dummy_561 f) ∈
      (((Class.cv (nb095_alpha_dummy_561 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_561 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0586 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_559 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_558 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_559 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0587 (f : Var) :
    (nb095_alpha_dummy_562 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_561 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_562 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0588 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_559 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_559 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_559 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0589 (f : Var) :
    (nb095_alpha_dummy_562 f) ∈
      (((Class.cv (nb095_alpha_dummy_562 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_562 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0590 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_386 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0591 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_386 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_543 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_543 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_386 D R S_cls E) ≠ (nb095_alpha_dummy_543 D R S_cls E) from (by
          unfold nb095_alpha_dummy_543;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0590 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_386 D R S_cls E) ≠ (nb095_alpha_dummy_544 D R S_cls E) from (by
            unfold nb095_alpha_dummy_544;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0590 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0592 (f : Var) :
    (nb095_alpha_dummy_389 f) ∈
      (((Class.cv (nb095_alpha_dummy_390 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_389 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0593 (f : Var) :
    (nb095_alpha_dummy_389 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_545 f)
              (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_390 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_545 f)
              (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_389 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_545 f) from (by
          unfold nb095_alpha_dummy_545;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0592 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_546 f) from (by
            unfold nb095_alpha_dummy_546;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0592 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0594 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_386 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_543 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_543 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_386 D R S_cls E) ≠ (nb095_alpha_dummy_543 D R S_cls E) from (by
          unfold nb095_alpha_dummy_543;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0590 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_386 D R S_cls E) ≠ (nb095_alpha_dummy_544 D R S_cls E) from (by
            unfold nb095_alpha_dummy_544;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0590 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0595 (f : Var) :
    (nb095_alpha_dummy_389 f) ∈
      (((Class.cab (nb095_alpha_dummy_545 f)
            (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_389 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_545 f)
            (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_389 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_545 f) from (by
          unfold nb095_alpha_dummy_545;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0592 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_546 f) from (by
            unfold nb095_alpha_dummy_546;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0592 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0596 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_544 D R S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0597 (f : Var) :
    (nb095_alpha_dummy_546 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_546 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0598 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_544 D R S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0599 (f : Var) :
    (nb095_alpha_dummy_546 f) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0600 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_002 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
            ((syn_cin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
          ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0601 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    x ∈
      (((Class.cv f)).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv x))))))).fv ∪ ((syn_cin S_cls (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv u))))))).fv ∪ ((syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
        ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv u))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0602 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_003 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0603 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_003 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_579 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_579 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_003 D R S_cls E) ≠ (nb095_alpha_dummy_579 D R S_cls E) from (by
          unfold nb095_alpha_dummy_579;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0602 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_003 D R S_cls E) ≠ (nb095_alpha_dummy_580 D R S_cls E) from (by
            unfold nb095_alpha_dummy_580;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0602 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0604 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_005 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0605 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_005 x u D R S_cls f E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E)) (syn_cphi
                    (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
          (nb095_alpha_dummy_581 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_581;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0604 x u D R S_cls f E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
            (nb095_alpha_dummy_582 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_582;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0604 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0606 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_003 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_579 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_579 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_003 D R S_cls E) ≠ (nb095_alpha_dummy_579 D R S_cls E) from (by
          unfold nb095_alpha_dummy_579;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0602 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_003 D R S_cls E) ≠ (nb095_alpha_dummy_580 D R S_cls E) from (by
            unfold nb095_alpha_dummy_580;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0602 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0607 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_005 x u D R S_cls f E) ∈
      (((Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
          (nb095_alpha_dummy_581 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_581;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0604 x u D R S_cls f E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
            (nb095_alpha_dummy_582 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_582;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0604 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0608 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_580 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_580 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0609 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_582 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0610 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_587 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_587 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_587 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_587 D R S_cls E))).fv) :=
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

theorem nb095_support_mem_0611 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_589 x u D R S_cls f E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv) :=
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

theorem nb095_support_mem_0612 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_587 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0613 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_589 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0614 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_594 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_594 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_595 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_594 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_595 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0615 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_597 x u D R S_cls f E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0616 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_594 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_594 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_595 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0617 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_597 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0618 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_595 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_594 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_595 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_594 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_595 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0619 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_598 x u D R S_cls f E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0620 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_595 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_594 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_595 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0621 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_598 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

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

theorem nb095_support_mem_0622 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_594 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_594 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_595 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0623 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_597 x u D R S_cls f E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0624 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_594 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_594 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_594 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0625 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_597 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0626 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_595 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_594 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_595 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0627 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_598 x u D R S_cls f E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0628 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_595 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_595 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_595 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0629 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_598 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0630 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_004 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0631 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_004 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_579 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_579 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_004 D R S_cls E) ≠ (nb095_alpha_dummy_579 D R S_cls E) from (by
          unfold nb095_alpha_dummy_579;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0630 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_004 D R S_cls E) ≠ (nb095_alpha_dummy_580 D R S_cls E) from (by
            unfold nb095_alpha_dummy_580;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0630 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0632 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_006 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0633 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_006 x u D R S_cls f E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E)) (syn_cphi
                    (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
          (nb095_alpha_dummy_581 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_581;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0632 x u D R S_cls f E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
            (nb095_alpha_dummy_582 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_582;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0632 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0634 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_004 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_579 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_579 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_004 D R S_cls E) ≠ (nb095_alpha_dummy_579 D R S_cls E) from (by
          unfold nb095_alpha_dummy_579;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0630 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_004 D R S_cls E) ≠ (nb095_alpha_dummy_580 D R S_cls E) from (by
            unfold nb095_alpha_dummy_580;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0630 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0635 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_006 x u D R S_cls f E) ∈
      (((Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
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
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
          (nb095_alpha_dummy_581 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_581;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0632 x u D R S_cls f E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
            (nb095_alpha_dummy_582 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_582;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0632 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0636 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_580 D R S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0637 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_582 x u D R S_cls f E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0638 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_580 D R S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0639 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_582 x u D R S_cls f E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0640 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_619 D R S_cls E) ∈
      (({(nb095_alpha_dummy_619 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_620 D R S_cls E)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb095_alpha_dummy_619 D R S_cls E)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))
            (Wff.classMem (Class.cv (nb095_alpha_dummy_620 D R S_cls E)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0641 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_621 x D R) ∈
      (({(nb095_alpha_dummy_621 x D R)} : Finset Var) ∪
          ({(nb095_alpha_dummy_622 x D R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb095_alpha_dummy_621 x D R)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))))
            (Wff.classMem (Class.cv (nb095_alpha_dummy_622 x D R)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0642 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_620 D R S_cls E) ∈
      (({(nb095_alpha_dummy_619 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_620 D R S_cls E)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb095_alpha_dummy_619 D R S_cls E)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))
            (Wff.classMem (Class.cv (nb095_alpha_dummy_620 D R S_cls E)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0643 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_622 x D R) ∈
      (({(nb095_alpha_dummy_621 x D R)} : Finset Var) ∪
          ({(nb095_alpha_dummy_622 x D R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb095_alpha_dummy_621 x D R)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))))
            (Wff.classMem (Class.cv (nb095_alpha_dummy_622 x D R)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0644 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_619 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_619 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_620 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0645 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_619 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_625 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_619 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_625 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_620 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_619 D R S_cls E) ≠ (nb095_alpha_dummy_625 D R S_cls E) from (by
          unfold nb095_alpha_dummy_625;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0644 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_619 D R S_cls E) ≠ (nb095_alpha_dummy_626 D R S_cls E) from (by
            unfold nb095_alpha_dummy_626;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0644 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0646 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_621 x D R) ∈
      (((Class.cv (nb095_alpha_dummy_621 x D R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_622 x D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0647 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_621 x D R) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_627 x D R)
              (syn_wrex (nb095_alpha_dummy_628 x D R) (Class.cv (nb095_alpha_dummy_621 x D R))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_627 x D R) (syn_wrex (nb095_alpha_dummy_628 x D R)
                (Class.cv (nb095_alpha_dummy_622 x D R))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_621 x D R) ≠ (nb095_alpha_dummy_627 x D R) from (by
          unfold nb095_alpha_dummy_627;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0646 x D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_621 x D R) ≠ (nb095_alpha_dummy_628 x D R) from (by
            unfold nb095_alpha_dummy_628;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0646 x D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0648 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_619 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_625 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_619 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_625 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_619 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_619 D R S_cls E) ≠ (nb095_alpha_dummy_625 D R S_cls E) from (by
          unfold nb095_alpha_dummy_625;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0644 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_619 D R S_cls E) ≠ (nb095_alpha_dummy_626 D R S_cls E) from (by
            unfold nb095_alpha_dummy_626;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0644 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0649 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_621 x D R) ∈
      (((Class.cab (nb095_alpha_dummy_627 x D R) (syn_wrex (nb095_alpha_dummy_628 x D R)
              (Class.cv (nb095_alpha_dummy_621 x D R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_627 x D R) (syn_wrex (nb095_alpha_dummy_628 x D R)
              (Class.cv (nb095_alpha_dummy_621 x D R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_621 x D R) ≠ (nb095_alpha_dummy_627 x D R) from (by
          unfold nb095_alpha_dummy_627;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0646 x D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_621 x D R) ≠ (nb095_alpha_dummy_628 x D R) from (by
            unfold nb095_alpha_dummy_628;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0646 x D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0650 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_626 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_626 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0651 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_628 x D R) ∈ (((Class.cv (nb095_alpha_dummy_628 x D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0652 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_633 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_633 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_633 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_633 D R S_cls E))).fv) :=
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

theorem nb095_support_mem_0653 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_635 x D R) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_635 x D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_635 x D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_635 x D R))).fv) :=
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

theorem nb095_support_mem_0654 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_633 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_633 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0655 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_635 x D R) ∈
      (((Class.cv (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0656 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_640 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_640 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_641 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_640 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_641 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0657 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_643 x D R) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_643 x D R))
            (Class.cv (nb095_alpha_dummy_644 x D R)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_643 x D R))
            (Class.cv (nb095_alpha_dummy_644 x D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0658 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_640 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_640 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_641 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0659 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_643 x D R) ∈
      (((Class.cv (nb095_alpha_dummy_643 x D R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_644 x D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0660 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_641 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_640 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_641 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_640 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_641 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0661 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_644 x D R) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_643 x D R))
            (Class.cv (nb095_alpha_dummy_644 x D R)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_643 x D R))
            (Class.cv (nb095_alpha_dummy_644 x D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0662 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_641 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_640 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_641 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0663 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_644 x D R) ∈
      (((Class.cv (nb095_alpha_dummy_643 x D R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_644 x D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0664 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_640 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_640 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_641 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0665 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_643 x D R) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_643 x D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_644 x D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0666 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_640 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_640 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_640 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0667 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_643 x D R) ∈
      (((Class.cv (nb095_alpha_dummy_643 x D R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_643 x D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0668 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_641 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_640 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_641 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0669 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_644 x D R) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_643 x D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_644 x D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0670 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_641 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_641 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_641 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0671 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_644 x D R) ∈
      (((Class.cv (nb095_alpha_dummy_644 x D R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_644 x D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0672 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_620 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_619 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_620 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0673 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_620 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_625 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_619 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_625 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_620 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_620 D R S_cls E) ≠ (nb095_alpha_dummy_625 D R S_cls E) from (by
          unfold nb095_alpha_dummy_625;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0672 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_620 D R S_cls E) ≠ (nb095_alpha_dummy_626 D R S_cls E) from (by
            unfold nb095_alpha_dummy_626;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0672 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0674 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_622 x D R) ∈
      (((Class.cv (nb095_alpha_dummy_621 x D R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_622 x D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0675 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_622 x D R) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_627 x D R)
              (syn_wrex (nb095_alpha_dummy_628 x D R) (Class.cv (nb095_alpha_dummy_621 x D R))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_627 x D R) (syn_wrex (nb095_alpha_dummy_628 x D R)
                (Class.cv (nb095_alpha_dummy_622 x D R))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_622 x D R) ≠ (nb095_alpha_dummy_627 x D R) from (by
          unfold nb095_alpha_dummy_627;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0674 x D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_622 x D R) ≠ (nb095_alpha_dummy_628 x D R) from (by
            unfold nb095_alpha_dummy_628;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0674 x D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0676 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_620 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_625 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_620 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_625 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_620 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_620 D R S_cls E) ≠ (nb095_alpha_dummy_625 D R S_cls E) from (by
          unfold nb095_alpha_dummy_625;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0672 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_620 D R S_cls E) ≠ (nb095_alpha_dummy_626 D R S_cls E) from (by
            unfold nb095_alpha_dummy_626;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0672 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0677 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_622 x D R) ∈
      (((Class.cab (nb095_alpha_dummy_627 x D R) (syn_wrex (nb095_alpha_dummy_628 x D R)
              (Class.cv (nb095_alpha_dummy_622 x D R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_627 x D R)
            (syn_wrex (nb095_alpha_dummy_628 x D R) (Class.cv (nb095_alpha_dummy_622 x D R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_622 x D R) ≠ (nb095_alpha_dummy_627 x D R) from (by
          unfold nb095_alpha_dummy_627;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0674 x D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_622 x D R) ≠ (nb095_alpha_dummy_628 x D R) from (by
            unfold nb095_alpha_dummy_628;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0674 x D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0678 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_626 D R S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0679 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_628 x D R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0680 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_626 D R S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0681 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_628 x D R) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0682 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_002 D R S_cls E) ∈
      (((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
        ((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0683 (x : Var) (D : Class) (R : Class) :
    x ∈
      (((syn_cnin R (syn_cxp (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))).fv ∪
        ((syn_cnin R (syn_cxp (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0684 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_002 D R S_cls E) ∈
      ((R).fv ∪ ((syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0685 (x : Var) (D : Class) (R : Class) :
    x ∈
      ((R).fv ∪ ((syn_cxp (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0686 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_002 D R S_cls E) ∈
      (({(nb095_alpha_dummy_619 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_620 D R S_cls E)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb095_alpha_dummy_619 D R S_cls E)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))
            (Wff.classMem (Class.cv (nb095_alpha_dummy_620 D R S_cls E)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0687 (x : Var) (D : Class) (R : Class) :
    x ∈
      (({(nb095_alpha_dummy_621 x D R)} : Finset Var) ∪
          ({(nb095_alpha_dummy_622 x D R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb095_alpha_dummy_621 x D R)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))))
            (Wff.classMem (Class.cv (nb095_alpha_dummy_622 x D R)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0688 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_002 D R S_cls E) ∈
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0689 (x : Var) (D : Class) (R : Class) :
    x ∈
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
        ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0690 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_003 D R S_cls E) ∈
      (((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))).fv ∪
        ((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0691 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_003 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_661 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
                (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                  (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_661 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
                (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                  (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_003 D R S_cls E) ≠ (nb095_alpha_dummy_661 D R S_cls E) from (by
          unfold nb095_alpha_dummy_661;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0690 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_003 D R S_cls E) ≠ (nb095_alpha_dummy_662 D R S_cls E) from (by
            unfold nb095_alpha_dummy_662;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0690 D R S_cls E) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0692 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_005 x u D R S_cls f E) ∈
      (((syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))).fv ∪
        ((syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0693 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_005 x u D R S_cls f E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E) (syn_cfv (Class.cv f)
                  (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E)) (syn_cphi
                    (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E) (syn_cfv (Class.cv f)
                  (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
          (nb095_alpha_dummy_663 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_663;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0692 x u D R S_cls f E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
            (nb095_alpha_dummy_664 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_664;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0692 x u D R S_cls f E) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0694 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_003 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_661 D R S_cls E)
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
                (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_003 D R S_cls E) ≠ (nb095_alpha_dummy_661 D R S_cls E) from (by
          unfold nb095_alpha_dummy_661;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0690 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_003 D R S_cls E) ≠ (nb095_alpha_dummy_662 D R S_cls E) from (by
            unfold nb095_alpha_dummy_662;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0690 D R S_cls E) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0695 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_005 x u D R S_cls f E) ∈
      (((Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
              (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
              (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
          (nb095_alpha_dummy_663 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_663;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0692 x u D R S_cls f E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
            (nb095_alpha_dummy_664 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_664;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0692 x u D R S_cls f E) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0696 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_003 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0697 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_003 D R S_cls E) ∈
      (({(nb095_alpha_dummy_669 D R S_cls E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_669 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0698 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_003 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_671 D R S_cls E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_669 D R S_cls E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_669 D R S_cls E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_671 D R S_cls E)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_003 D R S_cls E) ≠ (nb095_alpha_dummy_671 D R S_cls E) from (by
          unfold nb095_alpha_dummy_671;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0697 D R S_cls E) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_003 D R S_cls E) ≠ (nb095_alpha_dummy_669 D R S_cls E) from (by
            unfold nb095_alpha_dummy_669;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0696 D R S_cls E) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0699 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_005 x u D R S_cls f E) ∈
      (((Class.cv f)).fv ∪ ((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0700 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_005 x u D R S_cls f E) ∈
      (({(nb095_alpha_dummy_670 x u D R S_cls f E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)) (Class.cv f)
            (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0701 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_005 x u D R S_cls f E) ∈
      (((Class.cab (nb095_alpha_dummy_672 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_670 x u D R S_cls f E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_672 x u D R S_cls f E)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
          (nb095_alpha_dummy_672 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_672;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0700 x u D R S_cls f E) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
            (nb095_alpha_dummy_670 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_670;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0699 x u D R S_cls f E) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0702 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_003 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_669 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0703 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_003 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_677 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_677 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_669 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_003 D R S_cls E) ≠ (nb095_alpha_dummy_677 D R S_cls E) from (by
          unfold nb095_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0702 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_003 D R S_cls E) ≠ (nb095_alpha_dummy_678 D R S_cls E) from (by
            unfold nb095_alpha_dummy_678;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0702 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0704 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_005 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0705 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_005 x u D R S_cls f E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E)) (syn_cphi
                    (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
          (nb095_alpha_dummy_679 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0704 x u D R S_cls f E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
            (nb095_alpha_dummy_680 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_680;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0704 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0706 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_003 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_677 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_677 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_003 D R S_cls E) ≠ (nb095_alpha_dummy_677 D R S_cls E) from (by
          unfold nb095_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0702 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_003 D R S_cls E) ≠ (nb095_alpha_dummy_678 D R S_cls E) from (by
            unfold nb095_alpha_dummy_678;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0702 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0707 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_005 x u D R S_cls f E) ∈
      (((Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
          (nb095_alpha_dummy_679 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0704 x u D R S_cls f E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
            (nb095_alpha_dummy_680 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_680;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0704 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0708 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_678 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_678 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0709 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_680 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0710 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_685 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_685 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_685 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_685 D R S_cls E))).fv) :=
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

theorem nb095_support_mem_0711 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_687 x u D R S_cls f E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv) :=
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

theorem nb095_support_mem_0712 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_685 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_685 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0713 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_687 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0714 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_692 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_692 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_693 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_692 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_693 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0715 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_695 x u D R S_cls f E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0716 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_692 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_692 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_693 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0717 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_695 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0718 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_693 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_692 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_693 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_692 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_693 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0719 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_696 x u D R S_cls f E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0720 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_693 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_692 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_693 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0721 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_696 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0722 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_692 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_692 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_693 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0723 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_695 x u D R S_cls f E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0724 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_692 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_692 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_692 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
