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
    (nb095AlphaDummy339 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy345 D R S_cls E)
            (synWrex (nb095AlphaDummy346 D R S_cls E)
              (Class.cv (nb095AlphaDummy339 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy345 D R S_cls E)
            (synWrex (nb095AlphaDummy346 D R S_cls E)
              (Class.cv (nb095AlphaDummy339 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy339 D R S_cls E) ≠ (nb095AlphaDummy345 D R S_cls E) from (by
          unfold nb095AlphaDummy345;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0380 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy339 D R S_cls E) ≠ (nb095AlphaDummy346 D R S_cls E) from (by
            unfold nb095AlphaDummy346;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0380 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0385 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy341 u S_cls) ∈
      (((Class.cab (nb095AlphaDummy347 u S_cls) (synWrex (nb095AlphaDummy348 u S_cls)
              (Class.cv (nb095AlphaDummy341 u S_cls))
              (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
                (synCun (synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy347 u S_cls)
            (synWrex (nb095AlphaDummy348 u S_cls) (Class.cv (nb095AlphaDummy341 u S_cls))
              (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
                (synCun (synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy347 u S_cls) from (by
          unfold nb095AlphaDummy347;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0382 u S_cls) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy348 u S_cls) from (by
            unfold nb095AlphaDummy348;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0382 u S_cls) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0386 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy346 D R S_cls E) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0387 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy348 u S_cls) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy348 u S_cls))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0388 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy346 D R S_cls E) ∈
      (((synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0389 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy348 u S_cls) ∈
      (((synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0390 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy385 D R S_cls E) ∈
      (({(nb095AlphaDummy385 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy386 D R S_cls E)} : Finset Var) ∪
        ((synWex (nb095AlphaDummy387 D R S_cls E) (synWa
              (synWbr (Class.cv (nb095AlphaDummy385 D R S_cls E))
                (synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))
                (Class.cv (nb095AlphaDummy387 D R S_cls E)))
              (synWbr (Class.cv (nb095AlphaDummy387 D R S_cls E))
                (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
                (Class.cv (nb095AlphaDummy386 D R S_cls E)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0391 (f : Var) :
    (nb095AlphaDummy388 f) ∈
      (({(nb095AlphaDummy388 f)} : Finset Var) ∪ ({(nb095AlphaDummy389 f)} : Finset Var) ∪
        ((synWex (nb095AlphaDummy390 f) (synWa
              (synWbr (Class.cv (nb095AlphaDummy388 f))
                (synCcnv (synCcnv (Class.cv f))) (Class.cv (nb095AlphaDummy390 f)))
              (synWbr (Class.cv (nb095AlphaDummy390 f)) (synCcnv (Class.cv f))
                (Class.cv (nb095AlphaDummy389 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0392 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy386 D R S_cls E) ∈
      (({(nb095AlphaDummy385 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy386 D R S_cls E)} : Finset Var) ∪
        ((synWex (nb095AlphaDummy387 D R S_cls E) (synWa
              (synWbr (Class.cv (nb095AlphaDummy385 D R S_cls E))
                (synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))
                (Class.cv (nb095AlphaDummy387 D R S_cls E)))
              (synWbr (Class.cv (nb095AlphaDummy387 D R S_cls E))
                (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
                (Class.cv (nb095AlphaDummy386 D R S_cls E)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0393 (f : Var) :
    (nb095AlphaDummy389 f) ∈
      (({(nb095AlphaDummy388 f)} : Finset Var) ∪ ({(nb095AlphaDummy389 f)} : Finset Var) ∪
        ((synWex (nb095AlphaDummy390 f) (synWa
              (synWbr (Class.cv (nb095AlphaDummy388 f))
                (synCcnv (synCcnv (Class.cv f))) (Class.cv (nb095AlphaDummy390 f)))
              (synWbr (Class.cv (nb095AlphaDummy390 f)) (synCcnv (Class.cv f))
                (Class.cv (nb095AlphaDummy389 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0394 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy385 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0395 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy385 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy393 D R S_cls E)
              (synWrex (nb095AlphaDummy394 D R S_cls E)
                (Class.cv (nb095AlphaDummy385 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy393 D R S_cls E)
              (synWrex (nb095AlphaDummy394 D R S_cls E)
                (Class.cv (nb095AlphaDummy386 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy385 D R S_cls E) ≠ (nb095AlphaDummy393 D R S_cls E) from (by
          unfold nb095AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0394 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy385 D R S_cls E) ≠ (nb095AlphaDummy394 D R S_cls E) from (by
            unfold nb095AlphaDummy394;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0394 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0396 (f : Var) :
    (nb095AlphaDummy388 f) ∈
      (((Class.cv (nb095AlphaDummy388 f))).fv ∪ ((Class.cv (nb095AlphaDummy389 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0397 (f : Var) :
    (nb095AlphaDummy388 f) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy395 f)
              (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy388 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                  (synCphi (Class.cv (nb095AlphaDummy396 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy395 f)
              (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy389 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy396 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy388 f) ≠ (nb095AlphaDummy395 f) from (by
          unfold nb095AlphaDummy395;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0396 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy388 f) ≠ (nb095AlphaDummy396 f) from (by
            unfold nb095AlphaDummy396;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0396 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0398 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy385 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy393 D R S_cls E)
            (synWrex (nb095AlphaDummy394 D R S_cls E)
              (Class.cv (nb095AlphaDummy385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy393 D R S_cls E)
            (synWrex (nb095AlphaDummy394 D R S_cls E)
              (Class.cv (nb095AlphaDummy385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy385 D R S_cls E) ≠ (nb095AlphaDummy393 D R S_cls E) from (by
          unfold nb095AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0394 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy385 D R S_cls E) ≠ (nb095AlphaDummy394 D R S_cls E) from (by
            unfold nb095AlphaDummy394;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0394 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0399 (f : Var) :
    (nb095AlphaDummy388 f) ∈
      (((Class.cab (nb095AlphaDummy395 f)
            (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy388 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                (synCphi (Class.cv (nb095AlphaDummy396 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy395 f)
            (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy388 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                (synCphi (Class.cv (nb095AlphaDummy396 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy388 f) ≠ (nb095AlphaDummy395 f) from (by
          unfold nb095AlphaDummy395;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0396 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy388 f) ≠ (nb095AlphaDummy396 f) from (by
            unfold nb095AlphaDummy396;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0396 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0400 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy394 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy394 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0401 (f : Var) :
    (nb095AlphaDummy396 f) ∈ (((Class.cv (nb095AlphaDummy396 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0402 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy401 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy401 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy401 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy401 D R S_cls E))).fv) :=
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
    (nb095AlphaDummy403 f) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy403 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy403 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy403 f))).fv) :=
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
    (nb095AlphaDummy401 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy401 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0405 (f : Var) :
    (nb095AlphaDummy403 f) ∈
      (((Class.cv (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0406 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy408 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy408 D R S_cls E))
            (Class.cv (nb095AlphaDummy409 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy408 D R S_cls E))
            (Class.cv (nb095AlphaDummy409 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0407 (f : Var) :
    (nb095AlphaDummy411 f) ∈
      (((synCnin (Class.cv (nb095AlphaDummy411 f))
            (Class.cv (nb095AlphaDummy412 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy411 f))
            (Class.cv (nb095AlphaDummy412 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0408 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy408 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy408 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy409 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0409 (f : Var) :
    (nb095AlphaDummy411 f) ∈
      (((Class.cv (nb095AlphaDummy411 f))).fv ∪ ((Class.cv (nb095AlphaDummy412 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0410 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy409 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy408 D R S_cls E))
            (Class.cv (nb095AlphaDummy409 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy408 D R S_cls E))
            (Class.cv (nb095AlphaDummy409 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0411 (f : Var) :
    (nb095AlphaDummy412 f) ∈
      (((synCnin (Class.cv (nb095AlphaDummy411 f))
            (Class.cv (nb095AlphaDummy412 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy411 f))
            (Class.cv (nb095AlphaDummy412 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0412 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy409 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy408 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy409 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0413 (f : Var) :
    (nb095AlphaDummy412 f) ∈
      (((Class.cv (nb095AlphaDummy411 f))).fv ∪ ((Class.cv (nb095AlphaDummy412 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0414 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy408 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy408 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy409 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0415 (f : Var) :
    (nb095AlphaDummy411 f) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy411 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy412 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0416 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy408 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy408 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy408 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0417 (f : Var) :
    (nb095AlphaDummy411 f) ∈
      (((Class.cv (nb095AlphaDummy411 f))).fv ∪ ((Class.cv (nb095AlphaDummy411 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0418 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy409 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy408 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy409 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0419 (f : Var) :
    (nb095AlphaDummy412 f) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy411 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy412 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0420 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy409 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy409 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy409 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0421 (f : Var) :
    (nb095AlphaDummy412 f) ∈
      (((Class.cv (nb095AlphaDummy412 f))).fv ∪ ((Class.cv (nb095AlphaDummy412 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0422 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy386 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0423 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy386 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy393 D R S_cls E)
              (synWrex (nb095AlphaDummy394 D R S_cls E)
                (Class.cv (nb095AlphaDummy385 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy393 D R S_cls E)
              (synWrex (nb095AlphaDummy394 D R S_cls E)
                (Class.cv (nb095AlphaDummy386 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy393 D R S_cls E) from (by
          unfold nb095AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0422 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy394 D R S_cls E) from (by
            unfold nb095AlphaDummy394;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0422 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0424 (f : Var) :
    (nb095AlphaDummy389 f) ∈
      (((Class.cv (nb095AlphaDummy388 f))).fv ∪ ((Class.cv (nb095AlphaDummy389 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0425 (f : Var) :
    (nb095AlphaDummy389 f) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy395 f)
              (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy388 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                  (synCphi (Class.cv (nb095AlphaDummy396 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy395 f)
              (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy389 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy396 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy395 f) from (by
          unfold nb095AlphaDummy395;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0424 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy396 f) from (by
            unfold nb095AlphaDummy396;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0424 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0426 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy386 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy393 D R S_cls E)
            (synWrex (nb095AlphaDummy394 D R S_cls E)
              (Class.cv (nb095AlphaDummy386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy393 D R S_cls E)
            (synWrex (nb095AlphaDummy394 D R S_cls E)
              (Class.cv (nb095AlphaDummy386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy393 D R S_cls E) from (by
          unfold nb095AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0422 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy394 D R S_cls E) from (by
            unfold nb095AlphaDummy394;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0422 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0427 (f : Var) :
    (nb095AlphaDummy389 f) ∈
      (((Class.cab (nb095AlphaDummy395 f)
            (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy389 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy396 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy395 f)
            (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy389 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy396 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy395 f) from (by
          unfold nb095AlphaDummy395;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0424 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy396 f) from (by
            unfold nb095AlphaDummy396;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0424 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0428 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy394 D R S_cls E) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0429 (f : Var) :
    (nb095AlphaDummy396 f) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy396 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0430 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy394 D R S_cls E) ∈
      (((synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0431 (f : Var) :
    (nb095AlphaDummy396 f) ∈
      (((synCphi (Class.cv (nb095AlphaDummy396 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy396 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0432 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy385 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0433 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy385 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy429 D R S_cls E)
              (synWrex (nb095AlphaDummy430 D R S_cls E)
                (Class.cv (nb095AlphaDummy385 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy429 D R S_cls E)
              (synWrex (nb095AlphaDummy430 D R S_cls E)
                (Class.cv (nb095AlphaDummy387 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy385 D R S_cls E) ≠ (nb095AlphaDummy429 D R S_cls E) from (by
          unfold nb095AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0432 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy385 D R S_cls E) ≠ (nb095AlphaDummy430 D R S_cls E) from (by
            unfold nb095AlphaDummy430;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0432 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0434 (f : Var) :
    (nb095AlphaDummy388 f) ∈
      (((Class.cv (nb095AlphaDummy388 f))).fv ∪ ((Class.cv (nb095AlphaDummy390 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0435 (f : Var) :
    (nb095AlphaDummy388 f) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy431 f)
              (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy388 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                  (synCphi (Class.cv (nb095AlphaDummy432 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy431 f)
              (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy390 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy432 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy388 f) ≠ (nb095AlphaDummy431 f) from (by
          unfold nb095AlphaDummy431;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0434 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy388 f) ≠ (nb095AlphaDummy432 f) from (by
            unfold nb095AlphaDummy432;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0434 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0436 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy385 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy429 D R S_cls E)
            (synWrex (nb095AlphaDummy430 D R S_cls E)
              (Class.cv (nb095AlphaDummy385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy429 D R S_cls E)
            (synWrex (nb095AlphaDummy430 D R S_cls E)
              (Class.cv (nb095AlphaDummy385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy385 D R S_cls E) ≠ (nb095AlphaDummy429 D R S_cls E) from (by
          unfold nb095AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0432 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy385 D R S_cls E) ≠ (nb095AlphaDummy430 D R S_cls E) from (by
            unfold nb095AlphaDummy430;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0432 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0437 (f : Var) :
    (nb095AlphaDummy388 f) ∈
      (((Class.cab (nb095AlphaDummy431 f)
            (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy388 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                (synCphi (Class.cv (nb095AlphaDummy432 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy431 f)
            (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy388 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                (synCphi (Class.cv (nb095AlphaDummy432 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy388 f) ≠ (nb095AlphaDummy431 f) from (by
          unfold nb095AlphaDummy431;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0434 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy388 f) ≠ (nb095AlphaDummy432 f) from (by
            unfold nb095AlphaDummy432;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0434 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0438 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy430 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy430 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0439 (f : Var) :
    (nb095AlphaDummy432 f) ∈ (((Class.cv (nb095AlphaDummy432 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0440 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy437 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy437 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy437 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy437 D R S_cls E))).fv) :=
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
    (nb095AlphaDummy439 f) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy439 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy439 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy439 f))).fv) :=
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
    (nb095AlphaDummy437 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy437 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0443 (f : Var) :
    (nb095AlphaDummy439 f) ∈
      (((Class.cv (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0444 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy444 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy444 D R S_cls E))
            (Class.cv (nb095AlphaDummy445 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy444 D R S_cls E))
            (Class.cv (nb095AlphaDummy445 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0445 (f : Var) :
    (nb095AlphaDummy447 f) ∈
      (((synCnin (Class.cv (nb095AlphaDummy447 f))
            (Class.cv (nb095AlphaDummy448 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy447 f))
            (Class.cv (nb095AlphaDummy448 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0446 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy444 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy444 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy445 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0447 (f : Var) :
    (nb095AlphaDummy447 f) ∈
      (((Class.cv (nb095AlphaDummy447 f))).fv ∪ ((Class.cv (nb095AlphaDummy448 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0448 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy445 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy444 D R S_cls E))
            (Class.cv (nb095AlphaDummy445 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy444 D R S_cls E))
            (Class.cv (nb095AlphaDummy445 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0449 (f : Var) :
    (nb095AlphaDummy448 f) ∈
      (((synCnin (Class.cv (nb095AlphaDummy447 f))
            (Class.cv (nb095AlphaDummy448 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy447 f))
            (Class.cv (nb095AlphaDummy448 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0450 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy445 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy444 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy445 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0451 (f : Var) :
    (nb095AlphaDummy448 f) ∈
      (((Class.cv (nb095AlphaDummy447 f))).fv ∪ ((Class.cv (nb095AlphaDummy448 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0452 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy444 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy444 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy445 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0453 (f : Var) :
    (nb095AlphaDummy447 f) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy447 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy448 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0454 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy444 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy444 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy444 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0455 (f : Var) :
    (nb095AlphaDummy447 f) ∈
      (((Class.cv (nb095AlphaDummy447 f))).fv ∪ ((Class.cv (nb095AlphaDummy447 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0456 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy445 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy444 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy445 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0457 (f : Var) :
    (nb095AlphaDummy448 f) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy447 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy448 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0458 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy445 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy445 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy445 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0459 (f : Var) :
    (nb095AlphaDummy448 f) ∈
      (((Class.cv (nb095AlphaDummy448 f))).fv ∪ ((Class.cv (nb095AlphaDummy448 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0460 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy387 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0461 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy387 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy429 D R S_cls E)
              (synWrex (nb095AlphaDummy430 D R S_cls E)
                (Class.cv (nb095AlphaDummy385 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy429 D R S_cls E)
              (synWrex (nb095AlphaDummy430 D R S_cls E)
                (Class.cv (nb095AlphaDummy387 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy387 D R S_cls E) ≠ (nb095AlphaDummy429 D R S_cls E) from (by
          unfold nb095AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0460 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy387 D R S_cls E) ≠ (nb095AlphaDummy430 D R S_cls E) from (by
            unfold nb095AlphaDummy430;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0460 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0462 (f : Var) :
    (nb095AlphaDummy390 f) ∈
      (((Class.cv (nb095AlphaDummy388 f))).fv ∪ ((Class.cv (nb095AlphaDummy390 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0463 (f : Var) :
    (nb095AlphaDummy390 f) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy431 f)
              (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy388 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                  (synCphi (Class.cv (nb095AlphaDummy432 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy431 f)
              (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy390 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy432 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy431 f) from (by
          unfold nb095AlphaDummy431;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0462 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy432 f) from (by
            unfold nb095AlphaDummy432;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0462 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0464 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy387 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy429 D R S_cls E)
            (synWrex (nb095AlphaDummy430 D R S_cls E)
              (Class.cv (nb095AlphaDummy387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy429 D R S_cls E)
            (synWrex (nb095AlphaDummy430 D R S_cls E)
              (Class.cv (nb095AlphaDummy387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy387 D R S_cls E) ≠ (nb095AlphaDummy429 D R S_cls E) from (by
          unfold nb095AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0460 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy387 D R S_cls E) ≠ (nb095AlphaDummy430 D R S_cls E) from (by
            unfold nb095AlphaDummy430;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0460 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0465 (f : Var) :
    (nb095AlphaDummy390 f) ∈
      (((Class.cab (nb095AlphaDummy431 f)
            (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy390 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy432 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy431 f)
            (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy390 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy432 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy431 f) from (by
          unfold nb095AlphaDummy431;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0462 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy432 f) from (by
            unfold nb095AlphaDummy432;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0462 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0466 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy430 D R S_cls E) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0467 (f : Var) :
    (nb095AlphaDummy432 f) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy432 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0468 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy430 D R S_cls E) ∈
      (((synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0469 (f : Var) :
    (nb095AlphaDummy432 f) ∈
      (((synCphi (Class.cv (nb095AlphaDummy432 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy432 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0470 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy465 D R S_cls E) ∈
      (({(nb095AlphaDummy465 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy466 D R S_cls E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy466 D R S_cls E))
            (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
            (Class.cv (nb095AlphaDummy465 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0471 (f : Var) :
    (nb095AlphaDummy467 f) ∈
      (({(nb095AlphaDummy467 f)} : Finset Var) ∪ ({(nb095AlphaDummy468 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy468 f)) (synCcnv (Class.cv f))
            (Class.cv (nb095AlphaDummy467 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0472 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy466 D R S_cls E) ∈
      (({(nb095AlphaDummy465 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy466 D R S_cls E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy466 D R S_cls E))
            (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
            (Class.cv (nb095AlphaDummy465 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0473 (f : Var) :
    (nb095AlphaDummy468 f) ∈
      (({(nb095AlphaDummy467 f)} : Finset Var) ∪ ({(nb095AlphaDummy468 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy468 f)) (synCcnv (Class.cv f))
            (Class.cv (nb095AlphaDummy467 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0474 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy465 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0475 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy465 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy471 D R S_cls E)
              (synWrex (nb095AlphaDummy472 D R S_cls E)
                (Class.cv (nb095AlphaDummy465 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy471 D R S_cls E)
              (synWrex (nb095AlphaDummy472 D R S_cls E)
                (Class.cv (nb095AlphaDummy466 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy465 D R S_cls E) ≠ (nb095AlphaDummy471 D R S_cls E) from (by
          unfold nb095AlphaDummy471;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0474 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy465 D R S_cls E) ≠ (nb095AlphaDummy472 D R S_cls E) from (by
            unfold nb095AlphaDummy472;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0474 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0476 (f : Var) :
    (nb095AlphaDummy467 f) ∈
      (((Class.cv (nb095AlphaDummy467 f))).fv ∪ ((Class.cv (nb095AlphaDummy468 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0477 (f : Var) :
    (nb095AlphaDummy467 f) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy473 f)
              (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy467 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                  (synCphi (Class.cv (nb095AlphaDummy474 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy473 f)
              (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy468 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy474 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy473 f) from (by
          unfold nb095AlphaDummy473;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0476 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy474 f) from (by
            unfold nb095AlphaDummy474;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0476 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0478 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy465 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy471 D R S_cls E)
            (synWrex (nb095AlphaDummy472 D R S_cls E)
              (Class.cv (nb095AlphaDummy465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy471 D R S_cls E)
            (synWrex (nb095AlphaDummy472 D R S_cls E)
              (Class.cv (nb095AlphaDummy465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy465 D R S_cls E) ≠ (nb095AlphaDummy471 D R S_cls E) from (by
          unfold nb095AlphaDummy471;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0474 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy465 D R S_cls E) ≠ (nb095AlphaDummy472 D R S_cls E) from (by
            unfold nb095AlphaDummy472;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0474 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0479 (f : Var) :
    (nb095AlphaDummy467 f) ∈
      (((Class.cab (nb095AlphaDummy473 f)
            (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy467 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                (synCphi (Class.cv (nb095AlphaDummy474 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy473 f)
            (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy467 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                (synCphi (Class.cv (nb095AlphaDummy474 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy473 f) from (by
          unfold nb095AlphaDummy473;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0476 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy474 f) from (by
            unfold nb095AlphaDummy474;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0476 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0480 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy472 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy472 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0481 (f : Var) :
    (nb095AlphaDummy474 f) ∈ (((Class.cv (nb095AlphaDummy474 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0482 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy479 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy479 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy479 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy479 D R S_cls E))).fv) :=
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
    (nb095AlphaDummy481 f) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy481 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy481 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy481 f))).fv) :=
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
    (nb095AlphaDummy479 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy479 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0485 (f : Var) :
    (nb095AlphaDummy481 f) ∈
      (((Class.cv (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0486 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy486 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy486 D R S_cls E))
            (Class.cv (nb095AlphaDummy487 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy486 D R S_cls E))
            (Class.cv (nb095AlphaDummy487 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0487 (f : Var) :
    (nb095AlphaDummy489 f) ∈
      (((synCnin (Class.cv (nb095AlphaDummy489 f))
            (Class.cv (nb095AlphaDummy490 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy489 f))
            (Class.cv (nb095AlphaDummy490 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0488 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy486 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy486 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy487 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0489 (f : Var) :
    (nb095AlphaDummy489 f) ∈
      (((Class.cv (nb095AlphaDummy489 f))).fv ∪ ((Class.cv (nb095AlphaDummy490 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0490 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy487 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy486 D R S_cls E))
            (Class.cv (nb095AlphaDummy487 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy486 D R S_cls E))
            (Class.cv (nb095AlphaDummy487 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0491 (f : Var) :
    (nb095AlphaDummy490 f) ∈
      (((synCnin (Class.cv (nb095AlphaDummy489 f))
            (Class.cv (nb095AlphaDummy490 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy489 f))
            (Class.cv (nb095AlphaDummy490 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0492 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy487 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy486 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy487 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0493 (f : Var) :
    (nb095AlphaDummy490 f) ∈
      (((Class.cv (nb095AlphaDummy489 f))).fv ∪ ((Class.cv (nb095AlphaDummy490 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0494 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy486 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy486 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy487 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0495 (f : Var) :
    (nb095AlphaDummy489 f) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy489 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy490 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0496 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy486 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy486 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy486 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0497 (f : Var) :
    (nb095AlphaDummy489 f) ∈
      (((Class.cv (nb095AlphaDummy489 f))).fv ∪ ((Class.cv (nb095AlphaDummy489 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0498 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy487 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy486 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy487 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0499 (f : Var) :
    (nb095AlphaDummy490 f) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy489 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy490 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0500 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy487 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy487 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy487 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0501 (f : Var) :
    (nb095AlphaDummy490 f) ∈
      (((Class.cv (nb095AlphaDummy490 f))).fv ∪ ((Class.cv (nb095AlphaDummy490 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0502 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy466 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0503 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy466 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy471 D R S_cls E)
              (synWrex (nb095AlphaDummy472 D R S_cls E)
                (Class.cv (nb095AlphaDummy465 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy471 D R S_cls E)
              (synWrex (nb095AlphaDummy472 D R S_cls E)
                (Class.cv (nb095AlphaDummy466 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy466 D R S_cls E) ≠ (nb095AlphaDummy471 D R S_cls E) from (by
          unfold nb095AlphaDummy471;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0502 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy466 D R S_cls E) ≠ (nb095AlphaDummy472 D R S_cls E) from (by
            unfold nb095AlphaDummy472;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0502 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0504 (f : Var) :
    (nb095AlphaDummy468 f) ∈
      (((Class.cv (nb095AlphaDummy467 f))).fv ∪ ((Class.cv (nb095AlphaDummy468 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0505 (f : Var) :
    (nb095AlphaDummy468 f) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy473 f)
              (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy467 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                  (synCphi (Class.cv (nb095AlphaDummy474 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy473 f)
              (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy468 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy474 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy473 f) from (by
          unfold nb095AlphaDummy473;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0504 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy474 f) from (by
            unfold nb095AlphaDummy474;
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
    (nb095AlphaDummy466 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy471 D R S_cls E)
            (synWrex (nb095AlphaDummy472 D R S_cls E)
              (Class.cv (nb095AlphaDummy466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy471 D R S_cls E)
            (synWrex (nb095AlphaDummy472 D R S_cls E)
              (Class.cv (nb095AlphaDummy466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy466 D R S_cls E) ≠ (nb095AlphaDummy471 D R S_cls E) from (by
          unfold nb095AlphaDummy471;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0502 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy466 D R S_cls E) ≠ (nb095AlphaDummy472 D R S_cls E) from (by
            unfold nb095AlphaDummy472;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0502 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0507 (f : Var) :
    (nb095AlphaDummy468 f) ∈
      (((Class.cab (nb095AlphaDummy473 f)
            (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy468 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy474 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy473 f)
            (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy468 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy474 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy473 f) from (by
          unfold nb095AlphaDummy473;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0504 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy474 f) from (by
            unfold nb095AlphaDummy474;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0504 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0508 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy472 D R S_cls E) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0509 (f : Var) :
    (nb095AlphaDummy474 f) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy474 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0510 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy472 D R S_cls E) ∈
      (((synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0511 (f : Var) :
    (nb095AlphaDummy474 f) ∈
      (((synCphi (Class.cv (nb095AlphaDummy474 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy474 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0512 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy466 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0513 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy466 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy507 D R S_cls E)
              (synWrex (nb095AlphaDummy508 D R S_cls E)
                (Class.cv (nb095AlphaDummy466 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy507 D R S_cls E)
              (synWrex (nb095AlphaDummy508 D R S_cls E)
                (Class.cv (nb095AlphaDummy465 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy466 D R S_cls E) ≠ (nb095AlphaDummy507 D R S_cls E) from (by
          unfold nb095AlphaDummy507;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0512 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy466 D R S_cls E) ≠ (nb095AlphaDummy508 D R S_cls E) from (by
            unfold nb095AlphaDummy508;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0512 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0514 (f : Var) :
    (nb095AlphaDummy468 f) ∈
      (((Class.cv (nb095AlphaDummy468 f))).fv ∪ ((Class.cv (nb095AlphaDummy467 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0515 (f : Var) :
    (nb095AlphaDummy468 f) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy509 f)
              (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy468 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                  (synCphi (Class.cv (nb095AlphaDummy510 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy509 f)
              (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy467 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy510 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy509 f) from (by
          unfold nb095AlphaDummy509;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0514 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy510 f) from (by
            unfold nb095AlphaDummy510;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0514 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0516 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy466 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy507 D R S_cls E)
            (synWrex (nb095AlphaDummy508 D R S_cls E)
              (Class.cv (nb095AlphaDummy466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy507 D R S_cls E)
            (synWrex (nb095AlphaDummy508 D R S_cls E)
              (Class.cv (nb095AlphaDummy466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy466 D R S_cls E) ≠ (nb095AlphaDummy507 D R S_cls E) from (by
          unfold nb095AlphaDummy507;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0512 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy466 D R S_cls E) ≠ (nb095AlphaDummy508 D R S_cls E) from (by
            unfold nb095AlphaDummy508;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0512 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0517 (f : Var) :
    (nb095AlphaDummy468 f) ∈
      (((Class.cab (nb095AlphaDummy509 f)
            (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy468 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                (synCphi (Class.cv (nb095AlphaDummy510 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy509 f)
            (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy468 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                (synCphi (Class.cv (nb095AlphaDummy510 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy509 f) from (by
          unfold nb095AlphaDummy509;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0514 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy510 f) from (by
            unfold nb095AlphaDummy510;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0514 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0518 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy508 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy508 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0519 (f : Var) :
    (nb095AlphaDummy510 f) ∈ (((Class.cv (nb095AlphaDummy510 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0520 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy515 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy515 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy515 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy515 D R S_cls E))).fv) :=
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
    (nb095AlphaDummy517 f) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy517 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy517 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy517 f))).fv) :=
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
    (nb095AlphaDummy515 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy515 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0523 (f : Var) :
    (nb095AlphaDummy517 f) ∈
      (((Class.cv (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0524 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy522 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy522 D R S_cls E))
            (Class.cv (nb095AlphaDummy523 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy522 D R S_cls E))
            (Class.cv (nb095AlphaDummy523 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0525 (f : Var) :
    (nb095AlphaDummy525 f) ∈
      (((synCnin (Class.cv (nb095AlphaDummy525 f))
            (Class.cv (nb095AlphaDummy526 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy525 f))
            (Class.cv (nb095AlphaDummy526 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0526 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy522 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy522 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy523 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0527 (f : Var) :
    (nb095AlphaDummy525 f) ∈
      (((Class.cv (nb095AlphaDummy525 f))).fv ∪ ((Class.cv (nb095AlphaDummy526 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0528 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy523 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy522 D R S_cls E))
            (Class.cv (nb095AlphaDummy523 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy522 D R S_cls E))
            (Class.cv (nb095AlphaDummy523 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0529 (f : Var) :
    (nb095AlphaDummy526 f) ∈
      (((synCnin (Class.cv (nb095AlphaDummy525 f))
            (Class.cv (nb095AlphaDummy526 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy525 f))
            (Class.cv (nb095AlphaDummy526 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0530 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy523 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy522 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy523 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0531 (f : Var) :
    (nb095AlphaDummy526 f) ∈
      (((Class.cv (nb095AlphaDummy525 f))).fv ∪ ((Class.cv (nb095AlphaDummy526 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0532 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy522 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy522 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy523 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0533 (f : Var) :
    (nb095AlphaDummy525 f) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy525 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy526 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0534 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy522 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy522 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy522 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0535 (f : Var) :
    (nb095AlphaDummy525 f) ∈
      (((Class.cv (nb095AlphaDummy525 f))).fv ∪ ((Class.cv (nb095AlphaDummy525 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0536 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy523 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy522 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy523 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0537 (f : Var) :
    (nb095AlphaDummy526 f) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy525 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy526 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0538 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy523 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy523 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy523 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0539 (f : Var) :
    (nb095AlphaDummy526 f) ∈
      (((Class.cv (nb095AlphaDummy526 f))).fv ∪ ((Class.cv (nb095AlphaDummy526 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0540 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy465 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0541 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy465 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy507 D R S_cls E)
              (synWrex (nb095AlphaDummy508 D R S_cls E)
                (Class.cv (nb095AlphaDummy466 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy507 D R S_cls E)
              (synWrex (nb095AlphaDummy508 D R S_cls E)
                (Class.cv (nb095AlphaDummy465 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy465 D R S_cls E) ≠ (nb095AlphaDummy507 D R S_cls E) from (by
          unfold nb095AlphaDummy507;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0540 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy465 D R S_cls E) ≠ (nb095AlphaDummy508 D R S_cls E) from (by
            unfold nb095AlphaDummy508;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0540 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0542 (f : Var) :
    (nb095AlphaDummy467 f) ∈
      (((Class.cv (nb095AlphaDummy468 f))).fv ∪ ((Class.cv (nb095AlphaDummy467 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0543 (f : Var) :
    (nb095AlphaDummy467 f) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy509 f)
              (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy468 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                  (synCphi (Class.cv (nb095AlphaDummy510 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy509 f)
              (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy467 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy510 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy509 f) from (by
          unfold nb095AlphaDummy509;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0542 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy510 f) from (by
            unfold nb095AlphaDummy510;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0542 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0544 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy465 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy507 D R S_cls E)
            (synWrex (nb095AlphaDummy508 D R S_cls E)
              (Class.cv (nb095AlphaDummy465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy507 D R S_cls E)
            (synWrex (nb095AlphaDummy508 D R S_cls E)
              (Class.cv (nb095AlphaDummy465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy465 D R S_cls E) ≠ (nb095AlphaDummy507 D R S_cls E) from (by
          unfold nb095AlphaDummy507;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0540 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy465 D R S_cls E) ≠ (nb095AlphaDummy508 D R S_cls E) from (by
            unfold nb095AlphaDummy508;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0540 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0545 (f : Var) :
    (nb095AlphaDummy467 f) ∈
      (((Class.cab (nb095AlphaDummy509 f)
            (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy467 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy510 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy509 f)
            (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy467 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy510 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy509 f) from (by
          unfold nb095AlphaDummy509;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0542 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy510 f) from (by
            unfold nb095AlphaDummy510;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0542 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0546 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy508 D R S_cls E) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0547 (f : Var) :
    (nb095AlphaDummy510 f) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy510 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0548 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy508 D R S_cls E) ∈
      (((synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0549 (f : Var) :
    (nb095AlphaDummy510 f) ∈
      (((synCphi (Class.cv (nb095AlphaDummy510 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy510 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0550 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy000 D R S_cls E) ∈
      (((synCnin (synCcom (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
              (synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))))
            (synCid))).fv ∪ ((synCnin
            (synCcom (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
              (synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))))
            (synCid))).fv) :=
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
      (((synCnin (synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))
            (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))
            (synCid))).fv) :=
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
    (nb095AlphaDummy000 D R S_cls E) ∈
      (((synCcom (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
            (synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))))).fv ∪
        ((synCid)).fv) :=
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
      (((synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))).fv ∪
        ((synCid)).fv) :=
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
    (nb095AlphaDummy000 D R S_cls E) ∈
      (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0555 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy000 D R S_cls E) ∈
      (({(nb095AlphaDummy385 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy386 D R S_cls E)} : Finset Var) ∪
        ((synWex (nb095AlphaDummy387 D R S_cls E) (synWa
              (synWbr (Class.cv (nb095AlphaDummy385 D R S_cls E))
                (synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))
                (Class.cv (nb095AlphaDummy387 D R S_cls E)))
              (synWbr (Class.cv (nb095AlphaDummy387 D R S_cls E))
                (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
                (Class.cv (nb095AlphaDummy386 D R S_cls E)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy387 D R S_cls E) from (by
          unfold nb095AlphaDummy387;
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
    f ∈ (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0557 (f : Var) :
    f ∈
      (({(nb095AlphaDummy388 f)} : Finset Var) ∪ ({(nb095AlphaDummy389 f)} : Finset Var) ∪
        ((synWex (nb095AlphaDummy390 f) (synWa
              (synWbr (Class.cv (nb095AlphaDummy388 f))
                (synCcnv (synCcnv (Class.cv f))) (Class.cv (nb095AlphaDummy390 f)))
              (synWbr (Class.cv (nb095AlphaDummy390 f)) (synCcnv (Class.cv f))
                (Class.cv (nb095AlphaDummy389 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show f ≠ (nb095AlphaDummy390 f) from (by
          unfold nb095AlphaDummy390;
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
    (nb095AlphaDummy000 D R S_cls E) ∈
      (({(nb095AlphaDummy465 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy466 D R S_cls E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy466 D R S_cls E))
            (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
            (Class.cv (nb095AlphaDummy465 D R S_cls E)))).fv) :=
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
      (({(nb095AlphaDummy467 f)} : Finset Var) ∪ ({(nb095AlphaDummy468 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy468 f)) (synCcnv (Class.cv f))
            (Class.cv (nb095AlphaDummy467 f)))).fv) :=
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
    (nb095AlphaDummy000 D R S_cls E) ∈
      (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv) :=
  by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0561 (f : Var) : f ∈ (((synCcnv (Class.cv f))).fv) :=
  by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0562 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy387 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0563 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy387 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy543 D R S_cls E)
              (synWrex (nb095AlphaDummy544 D R S_cls E)
                (Class.cv (nb095AlphaDummy387 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy543 D R S_cls E)
              (synWrex (nb095AlphaDummy544 D R S_cls E)
                (Class.cv (nb095AlphaDummy386 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy387 D R S_cls E) ≠ (nb095AlphaDummy543 D R S_cls E) from (by
          unfold nb095AlphaDummy543;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy387 D R S_cls E) ≠ (nb095AlphaDummy544 D R S_cls E) from (by
            unfold nb095AlphaDummy544;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0564 (f : Var) :
    (nb095AlphaDummy390 f) ∈
      (((Class.cv (nb095AlphaDummy390 f))).fv ∪ ((Class.cv (nb095AlphaDummy389 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0565 (f : Var) :
    (nb095AlphaDummy390 f) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy545 f)
              (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy390 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                  (synCphi (Class.cv (nb095AlphaDummy546 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy545 f)
              (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy389 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy546 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy545 f) from (by
          unfold nb095AlphaDummy545;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0564 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy546 f) from (by
            unfold nb095AlphaDummy546;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0564 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0566 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy387 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy543 D R S_cls E)
            (synWrex (nb095AlphaDummy544 D R S_cls E)
              (Class.cv (nb095AlphaDummy387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy543 D R S_cls E)
            (synWrex (nb095AlphaDummy544 D R S_cls E)
              (Class.cv (nb095AlphaDummy387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy387 D R S_cls E) ≠ (nb095AlphaDummy543 D R S_cls E) from (by
          unfold nb095AlphaDummy543;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy387 D R S_cls E) ≠ (nb095AlphaDummy544 D R S_cls E) from (by
            unfold nb095AlphaDummy544;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0567 (f : Var) :
    (nb095AlphaDummy390 f) ∈
      (((Class.cab (nb095AlphaDummy545 f)
            (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy390 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                (synCphi (Class.cv (nb095AlphaDummy546 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy545 f)
            (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy390 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                (synCphi (Class.cv (nb095AlphaDummy546 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy545 f) from (by
          unfold nb095AlphaDummy545;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0564 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy546 f) from (by
            unfold nb095AlphaDummy546;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0564 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0568 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy544 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy544 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0569 (f : Var) :
    (nb095AlphaDummy546 f) ∈ (((Class.cv (nb095AlphaDummy546 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0570 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy551 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy551 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy551 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy551 D R S_cls E))).fv) :=
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
    (nb095AlphaDummy553 f) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy553 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy553 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy553 f))).fv) :=
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
    (nb095AlphaDummy551 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0573 (f : Var) :
    (nb095AlphaDummy553 f) ∈
      (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0574 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy558 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy558 D R S_cls E))
            (Class.cv (nb095AlphaDummy559 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy558 D R S_cls E))
            (Class.cv (nb095AlphaDummy559 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0575 (f : Var) :
    (nb095AlphaDummy561 f) ∈
      (((synCnin (Class.cv (nb095AlphaDummy561 f))
            (Class.cv (nb095AlphaDummy562 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy561 f))
            (Class.cv (nb095AlphaDummy562 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0576 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy558 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy558 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy559 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0577 (f : Var) :
    (nb095AlphaDummy561 f) ∈
      (((Class.cv (nb095AlphaDummy561 f))).fv ∪ ((Class.cv (nb095AlphaDummy562 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0578 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy559 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy558 D R S_cls E))
            (Class.cv (nb095AlphaDummy559 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy558 D R S_cls E))
            (Class.cv (nb095AlphaDummy559 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0579 (f : Var) :
    (nb095AlphaDummy562 f) ∈
      (((synCnin (Class.cv (nb095AlphaDummy561 f))
            (Class.cv (nb095AlphaDummy562 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy561 f))
            (Class.cv (nb095AlphaDummy562 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0580 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy559 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy558 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy559 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0581 (f : Var) :
    (nb095AlphaDummy562 f) ∈
      (((Class.cv (nb095AlphaDummy561 f))).fv ∪ ((Class.cv (nb095AlphaDummy562 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0582 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy558 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy558 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy559 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0583 (f : Var) :
    (nb095AlphaDummy561 f) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy561 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy562 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0584 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy558 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy558 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy558 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0585 (f : Var) :
    (nb095AlphaDummy561 f) ∈
      (((Class.cv (nb095AlphaDummy561 f))).fv ∪ ((Class.cv (nb095AlphaDummy561 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0586 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy559 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy558 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy559 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0587 (f : Var) :
    (nb095AlphaDummy562 f) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy561 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy562 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0588 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy559 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy559 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy559 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0589 (f : Var) :
    (nb095AlphaDummy562 f) ∈
      (((Class.cv (nb095AlphaDummy562 f))).fv ∪ ((Class.cv (nb095AlphaDummy562 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0590 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy386 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0591 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy386 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy543 D R S_cls E)
              (synWrex (nb095AlphaDummy544 D R S_cls E)
                (Class.cv (nb095AlphaDummy387 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy543 D R S_cls E)
              (synWrex (nb095AlphaDummy544 D R S_cls E)
                (Class.cv (nb095AlphaDummy386 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy543 D R S_cls E) from (by
          unfold nb095AlphaDummy543;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0590 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy544 D R S_cls E) from (by
            unfold nb095AlphaDummy544;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0590 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0592 (f : Var) :
    (nb095AlphaDummy389 f) ∈
      (((Class.cv (nb095AlphaDummy390 f))).fv ∪ ((Class.cv (nb095AlphaDummy389 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0593 (f : Var) :
    (nb095AlphaDummy389 f) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy545 f)
              (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy390 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                  (synCphi (Class.cv (nb095AlphaDummy546 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy545 f)
              (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy389 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy546 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy545 f) from (by
          unfold nb095AlphaDummy545;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0592 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy546 f) from (by
            unfold nb095AlphaDummy546;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0592 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0594 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy386 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy543 D R S_cls E)
            (synWrex (nb095AlphaDummy544 D R S_cls E)
              (Class.cv (nb095AlphaDummy386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy543 D R S_cls E)
            (synWrex (nb095AlphaDummy544 D R S_cls E)
              (Class.cv (nb095AlphaDummy386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy543 D R S_cls E) from (by
          unfold nb095AlphaDummy543;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0590 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy544 D R S_cls E) from (by
            unfold nb095AlphaDummy544;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0590 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0595 (f : Var) :
    (nb095AlphaDummy389 f) ∈
      (((Class.cab (nb095AlphaDummy545 f)
            (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy389 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy546 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy545 f)
            (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy389 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy546 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy545 f) from (by
          unfold nb095AlphaDummy545;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0592 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy546 f) from (by
            unfold nb095AlphaDummy546;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0592 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0596 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy544 D R S_cls E) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0597 (f : Var) :
    (nb095AlphaDummy546 f) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy546 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0598 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy544 D R S_cls E) ∈
      (((synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0599 (f : Var) :
    (nb095AlphaDummy546 f) ∈
      (((synCphi (Class.cv (nb095AlphaDummy546 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy546 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0600 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy002 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪
            ((synCin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                    (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
          ((synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv) :=
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
      (((Class.cv f)).fv ∪ ((synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv x))))))).fv ∪ ((synCin S_cls (synCxp (synCin E
                    (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
                  (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv u))))))).fv ∪ ((synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
        ((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv u))))).fv) :=
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
    (nb095AlphaDummy003 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0603 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy003 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy579 D R S_cls E)
              (synWrex (nb095AlphaDummy580 D R S_cls E)
                (Class.cv (nb095AlphaDummy003 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy579 D R S_cls E)
              (synWrex (nb095AlphaDummy580 D R S_cls E)
                (Class.cv (nb095AlphaDummy004 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy003 D R S_cls E) ≠ (nb095AlphaDummy579 D R S_cls E) from (by
          unfold nb095AlphaDummy579;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0602 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy003 D R S_cls E) ≠ (nb095AlphaDummy580 D R S_cls E) from (by
            unfold nb095AlphaDummy580;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0602 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0604 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy005 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0605 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy005 x u D R S_cls f E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E)) (synCphi
                    (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
          (nb095AlphaDummy581 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy581;
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
        (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
            (nb095AlphaDummy582 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy582;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0604 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0606 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy003 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy579 D R S_cls E)
            (synWrex (nb095AlphaDummy580 D R S_cls E)
              (Class.cv (nb095AlphaDummy003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy579 D R S_cls E)
            (synWrex (nb095AlphaDummy580 D R S_cls E)
              (Class.cv (nb095AlphaDummy003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy003 D R S_cls E) ≠ (nb095AlphaDummy579 D R S_cls E) from (by
          unfold nb095AlphaDummy579;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0602 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy003 D R S_cls E) ≠ (nb095AlphaDummy580 D R S_cls E) from (by
            unfold nb095AlphaDummy580;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0602 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0607 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy005 x u D R S_cls f E) ∈
      (((Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
          (nb095AlphaDummy581 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy581;
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
        (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
            (nb095AlphaDummy582 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy582;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0604 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0608 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy580 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy580 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0609 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy582 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy582 x u D R S_cls f E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0610 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy587 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy587 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy587 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy587 D R S_cls E))).fv) :=
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
    (nb095AlphaDummy589 x u D R S_cls f E) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy589 x u D R S_cls f E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy589 x u D R S_cls f E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv) :=
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
    (nb095AlphaDummy587 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0613 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy589 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0614 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy594 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy594 D R S_cls E))
            (Class.cv (nb095AlphaDummy595 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy594 D R S_cls E))
            (Class.cv (nb095AlphaDummy595 D R S_cls E)))).fv) :=
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
    (nb095AlphaDummy597 x u D R S_cls f E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy597 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy598 x u D R S_cls f E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy597 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy598 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0616 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy594 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy594 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy595 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0617 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy597 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy597 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy598 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0618 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy595 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy594 D R S_cls E))
            (Class.cv (nb095AlphaDummy595 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy594 D R S_cls E))
            (Class.cv (nb095AlphaDummy595 D R S_cls E)))).fv) :=
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
    (nb095AlphaDummy598 x u D R S_cls f E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy597 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy598 x u D R S_cls f E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy597 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy598 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0620 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy595 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy594 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy595 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0621 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy598 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy597 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy598 x u D R S_cls f E))).fv) :=
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
    (nb095AlphaDummy594 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy594 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy595 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0623 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy597 x u D R S_cls f E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy597 x u D R S_cls f E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy598 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0624 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy594 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy594 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy594 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0625 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy597 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy597 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy597 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0626 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy595 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy594 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy595 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0627 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy598 x u D R S_cls f E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy597 x u D R S_cls f E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy598 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0628 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy595 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy595 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy595 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0629 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy598 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy598 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy598 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0630 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy004 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0631 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy004 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy579 D R S_cls E)
              (synWrex (nb095AlphaDummy580 D R S_cls E)
                (Class.cv (nb095AlphaDummy003 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy579 D R S_cls E)
              (synWrex (nb095AlphaDummy580 D R S_cls E)
                (Class.cv (nb095AlphaDummy004 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy004 D R S_cls E) ≠ (nb095AlphaDummy579 D R S_cls E) from (by
          unfold nb095AlphaDummy579;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0630 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy004 D R S_cls E) ≠ (nb095AlphaDummy580 D R S_cls E) from (by
            unfold nb095AlphaDummy580;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0630 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0632 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy006 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0633 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy006 x u D R S_cls f E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E)) (synCphi
                    (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
          (nb095AlphaDummy581 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy581;
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
        (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
            (nb095AlphaDummy582 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy582;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0632 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0634 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy004 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy579 D R S_cls E)
            (synWrex (nb095AlphaDummy580 D R S_cls E)
              (Class.cv (nb095AlphaDummy004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy579 D R S_cls E)
            (synWrex (nb095AlphaDummy580 D R S_cls E)
              (Class.cv (nb095AlphaDummy004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy004 D R S_cls E) ≠ (nb095AlphaDummy579 D R S_cls E) from (by
          unfold nb095AlphaDummy579;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0630 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy004 D R S_cls E) ≠ (nb095AlphaDummy580 D R S_cls E) from (by
            unfold nb095AlphaDummy580;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0630 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0635 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy006 x u D R S_cls f E) ∈
      (((Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
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
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
          (nb095AlphaDummy581 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy581;
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
        (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
            (nb095AlphaDummy582 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy582;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0632 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0636 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy580 D R S_cls E) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0637 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy582 x u D R S_cls f E) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0638 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy580 D R S_cls E) ∈
      (((synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0639 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy582 x u D R S_cls f E) ∈
      (((synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0640 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy619 D R S_cls E) ∈
      (({(nb095AlphaDummy619 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy620 D R S_cls E)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb095AlphaDummy619 D R S_cls E)) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))
            (Wff.classMem (Class.cv (nb095AlphaDummy620 D R S_cls E)) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0641 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy621 x D R) ∈
      (({(nb095AlphaDummy621 x D R)} : Finset Var) ∪
          ({(nb095AlphaDummy622 x D R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb095AlphaDummy621 x D R)) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))))
            (Wff.classMem (Class.cv (nb095AlphaDummy622 x D R)) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0642 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy620 D R S_cls E) ∈
      (({(nb095AlphaDummy619 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy620 D R S_cls E)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb095AlphaDummy619 D R S_cls E)) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))
            (Wff.classMem (Class.cv (nb095AlphaDummy620 D R S_cls E)) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0643 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy622 x D R) ∈
      (({(nb095AlphaDummy621 x D R)} : Finset Var) ∪
          ({(nb095AlphaDummy622 x D R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb095AlphaDummy621 x D R)) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))))
            (Wff.classMem (Class.cv (nb095AlphaDummy622 x D R)) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0644 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy619 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy619 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy620 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0645 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy619 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy625 D R S_cls E)
              (synWrex (nb095AlphaDummy626 D R S_cls E)
                (Class.cv (nb095AlphaDummy619 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy625 D R S_cls E)
              (synWrex (nb095AlphaDummy626 D R S_cls E)
                (Class.cv (nb095AlphaDummy620 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy619 D R S_cls E) ≠ (nb095AlphaDummy625 D R S_cls E) from (by
          unfold nb095AlphaDummy625;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0644 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy619 D R S_cls E) ≠ (nb095AlphaDummy626 D R S_cls E) from (by
            unfold nb095AlphaDummy626;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0644 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0646 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy621 x D R) ∈
      (((Class.cv (nb095AlphaDummy621 x D R))).fv ∪
        ((Class.cv (nb095AlphaDummy622 x D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0647 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy621 x D R) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy627 x D R)
              (synWrex (nb095AlphaDummy628 x D R) (Class.cv (nb095AlphaDummy621 x D R))
                (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                  (synCphi (Class.cv (nb095AlphaDummy628 x D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy627 x D R) (synWrex (nb095AlphaDummy628 x D R)
                (Class.cv (nb095AlphaDummy622 x D R))
                (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy628 x D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy621 x D R) ≠ (nb095AlphaDummy627 x D R) from (by
          unfold nb095AlphaDummy627;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0646 x D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy621 x D R) ≠ (nb095AlphaDummy628 x D R) from (by
            unfold nb095AlphaDummy628;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0646 x D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0648 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy619 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy625 D R S_cls E)
            (synWrex (nb095AlphaDummy626 D R S_cls E)
              (Class.cv (nb095AlphaDummy619 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy625 D R S_cls E)
            (synWrex (nb095AlphaDummy626 D R S_cls E)
              (Class.cv (nb095AlphaDummy619 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy619 D R S_cls E) ≠ (nb095AlphaDummy625 D R S_cls E) from (by
          unfold nb095AlphaDummy625;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0644 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy619 D R S_cls E) ≠ (nb095AlphaDummy626 D R S_cls E) from (by
            unfold nb095AlphaDummy626;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0644 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0649 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy621 x D R) ∈
      (((Class.cab (nb095AlphaDummy627 x D R) (synWrex (nb095AlphaDummy628 x D R)
              (Class.cv (nb095AlphaDummy621 x D R))
              (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                (synCphi (Class.cv (nb095AlphaDummy628 x D R))))))).fv ∪
        ((Class.cab (nb095AlphaDummy627 x D R) (synWrex (nb095AlphaDummy628 x D R)
              (Class.cv (nb095AlphaDummy621 x D R))
              (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                (synCphi (Class.cv (nb095AlphaDummy628 x D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy621 x D R) ≠ (nb095AlphaDummy627 x D R) from (by
          unfold nb095AlphaDummy627;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0646 x D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy621 x D R) ≠ (nb095AlphaDummy628 x D R) from (by
            unfold nb095AlphaDummy628;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0646 x D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0650 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy626 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy626 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0651 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy628 x D R) ∈ (((Class.cv (nb095AlphaDummy628 x D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0652 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy633 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy633 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy633 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy633 D R S_cls E))).fv) :=
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
    (nb095AlphaDummy635 x D R) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy635 x D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy635 x D R)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy635 x D R))).fv) :=
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
    (nb095AlphaDummy633 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy633 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0655 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy635 x D R) ∈
      (((Class.cv (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0656 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy640 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy640 D R S_cls E))
            (Class.cv (nb095AlphaDummy641 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy640 D R S_cls E))
            (Class.cv (nb095AlphaDummy641 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0657 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy643 x D R) ∈
      (((synCnin (Class.cv (nb095AlphaDummy643 x D R))
            (Class.cv (nb095AlphaDummy644 x D R)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy643 x D R))
            (Class.cv (nb095AlphaDummy644 x D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0658 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy640 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy640 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy641 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0659 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy643 x D R) ∈
      (((Class.cv (nb095AlphaDummy643 x D R))).fv ∪
        ((Class.cv (nb095AlphaDummy644 x D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0660 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy641 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy640 D R S_cls E))
            (Class.cv (nb095AlphaDummy641 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy640 D R S_cls E))
            (Class.cv (nb095AlphaDummy641 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0661 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy644 x D R) ∈
      (((synCnin (Class.cv (nb095AlphaDummy643 x D R))
            (Class.cv (nb095AlphaDummy644 x D R)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy643 x D R))
            (Class.cv (nb095AlphaDummy644 x D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0662 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy641 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy640 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy641 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0663 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy644 x D R) ∈
      (((Class.cv (nb095AlphaDummy643 x D R))).fv ∪
        ((Class.cv (nb095AlphaDummy644 x D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0664 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy640 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy640 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy641 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0665 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy643 x D R) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy643 x D R)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy644 x D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0666 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy640 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy640 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy640 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0667 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy643 x D R) ∈
      (((Class.cv (nb095AlphaDummy643 x D R))).fv ∪
        ((Class.cv (nb095AlphaDummy643 x D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0668 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy641 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy640 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy641 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0669 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy644 x D R) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy643 x D R)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy644 x D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0670 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy641 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy641 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy641 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0671 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy644 x D R) ∈
      (((Class.cv (nb095AlphaDummy644 x D R))).fv ∪
        ((Class.cv (nb095AlphaDummy644 x D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0672 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy620 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy619 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy620 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0673 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy620 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy625 D R S_cls E)
              (synWrex (nb095AlphaDummy626 D R S_cls E)
                (Class.cv (nb095AlphaDummy619 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy625 D R S_cls E)
              (synWrex (nb095AlphaDummy626 D R S_cls E)
                (Class.cv (nb095AlphaDummy620 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy620 D R S_cls E) ≠ (nb095AlphaDummy625 D R S_cls E) from (by
          unfold nb095AlphaDummy625;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0672 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy620 D R S_cls E) ≠ (nb095AlphaDummy626 D R S_cls E) from (by
            unfold nb095AlphaDummy626;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0672 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0674 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy622 x D R) ∈
      (((Class.cv (nb095AlphaDummy621 x D R))).fv ∪
        ((Class.cv (nb095AlphaDummy622 x D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0675 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy622 x D R) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy627 x D R)
              (synWrex (nb095AlphaDummy628 x D R) (Class.cv (nb095AlphaDummy621 x D R))
                (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                  (synCphi (Class.cv (nb095AlphaDummy628 x D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy627 x D R) (synWrex (nb095AlphaDummy628 x D R)
                (Class.cv (nb095AlphaDummy622 x D R))
                (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy628 x D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy627 x D R) from (by
          unfold nb095AlphaDummy627;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0674 x D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy628 x D R) from (by
            unfold nb095AlphaDummy628;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0674 x D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0676 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy620 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy625 D R S_cls E)
            (synWrex (nb095AlphaDummy626 D R S_cls E)
              (Class.cv (nb095AlphaDummy620 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy625 D R S_cls E)
            (synWrex (nb095AlphaDummy626 D R S_cls E)
              (Class.cv (nb095AlphaDummy620 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy620 D R S_cls E) ≠ (nb095AlphaDummy625 D R S_cls E) from (by
          unfold nb095AlphaDummy625;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0672 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy620 D R S_cls E) ≠ (nb095AlphaDummy626 D R S_cls E) from (by
            unfold nb095AlphaDummy626;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0672 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0677 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy622 x D R) ∈
      (((Class.cab (nb095AlphaDummy627 x D R) (synWrex (nb095AlphaDummy628 x D R)
              (Class.cv (nb095AlphaDummy622 x D R))
              (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                (synCun (synCphi (Class.cv (nb095AlphaDummy628 x D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy627 x D R)
            (synWrex (nb095AlphaDummy628 x D R) (Class.cv (nb095AlphaDummy622 x D R))
              (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                (synCun (synCphi (Class.cv (nb095AlphaDummy628 x D R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy627 x D R) from (by
          unfold nb095AlphaDummy627;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0674 x D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy628 x D R) from (by
            unfold nb095AlphaDummy628;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0674 x D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0678 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy626 D R S_cls E) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0679 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy628 x D R) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy628 x D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0680 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy626 D R S_cls E) ∈
      (((synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0681 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy628 x D R) ∈
      (((synCphi (Class.cv (nb095AlphaDummy628 x D R)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy628 x D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0682 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy002 D R S_cls E) ∈
      (((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪
        ((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv) :=
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
      (((synCnin R (synCxp (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))).fv ∪
        ((synCnin R (synCxp (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))).fv) :=
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
    (nb095AlphaDummy002 D R S_cls E) ∈
      ((R).fv ∪ ((synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))).fv) :=
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
      ((R).fv ∪ ((synCxp (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))) (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))))).fv) :=
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
    (nb095AlphaDummy002 D R S_cls E) ∈
      (({(nb095AlphaDummy619 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy620 D R S_cls E)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb095AlphaDummy619 D R S_cls E)) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))
            (Wff.classMem (Class.cv (nb095AlphaDummy620 D R S_cls E)) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv) :=
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
      (({(nb095AlphaDummy621 x D R)} : Finset Var) ∪
          ({(nb095AlphaDummy622 x D R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb095AlphaDummy621 x D R)) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))))
            (Wff.classMem (Class.cv (nb095AlphaDummy622 x D R)) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))).fv) :=
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
    (nb095AlphaDummy002 D R S_cls E) ∈
      (((synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv) :=
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
      (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
        ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv) :=
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
    (nb095AlphaDummy003 D R S_cls E) ∈
      (((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy003 D R S_cls E)))).fv ∪
        ((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy004 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0691 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy003 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy661 D R S_cls E)
              (synWrex (nb095AlphaDummy662 D R S_cls E)
                (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                  (Class.cv (nb095AlphaDummy003 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy661 D R S_cls E)
              (synWrex (nb095AlphaDummy662 D R S_cls E)
                (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                  (Class.cv (nb095AlphaDummy004 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy003 D R S_cls E) ≠ (nb095AlphaDummy661 D R S_cls E) from (by
          unfold nb095AlphaDummy661;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0690 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy003 D R S_cls E) ≠ (nb095AlphaDummy662 D R S_cls E) from (by
            unfold nb095AlphaDummy662;
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
    (nb095AlphaDummy005 x u D R S_cls f E) ∈
      (((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))).fv ∪
        ((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))).fv) :=
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
    (nb095AlphaDummy005 x u D R S_cls f E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy664 x u D R S_cls f E) (synCfv (Class.cv f)
                  (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E)) (synCphi
                    (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy664 x u D R S_cls f E) (synCfv (Class.cv f)
                  (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
          (nb095AlphaDummy663 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy663;
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
        (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
            (nb095AlphaDummy664 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy664;
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
    (nb095AlphaDummy003 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy661 D R S_cls E)
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
                (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy003 D R S_cls E) ≠ (nb095AlphaDummy661 D R S_cls E) from (by
          unfold nb095AlphaDummy661;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0690 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy003 D R S_cls E) ≠ (nb095AlphaDummy662 D R S_cls E) from (by
            unfold nb095AlphaDummy662;
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
    (nb095AlphaDummy005 x u D R S_cls f E) ∈
      (((Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
          (nb095AlphaDummy663 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy663;
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
        (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
            (nb095AlphaDummy664 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy664;
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
    (nb095AlphaDummy003 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0697 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy003 D R S_cls E) ∈
      (({(nb095AlphaDummy669 D R S_cls E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy003 D R S_cls E))
            (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy669 D R S_cls E)))).fv) :=
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
    (nb095AlphaDummy003 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy671 D R S_cls E) (Wff.classEq
            (Class.cab (nb095AlphaDummy669 D R S_cls E)
              (synWbr (Class.cv (nb095AlphaDummy003 D R S_cls E))
                (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy669 D R S_cls E))))
            (synCsn (Class.cv (nb095AlphaDummy671 D R S_cls E)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy003 D R S_cls E) ≠ (nb095AlphaDummy671 D R S_cls E) from (by
          unfold nb095AlphaDummy671;
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
        (show (nb095AlphaDummy003 D R S_cls E) ≠ (nb095AlphaDummy669 D R S_cls E) from (by
            unfold nb095AlphaDummy669;
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
    (nb095AlphaDummy005 x u D R S_cls f E) ∈
      (((Class.cv f)).fv ∪ ((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0700 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy005 x u D R S_cls f E) ∈
      (({(nb095AlphaDummy670 x u D R S_cls f E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)) (Class.cv f)
            (Class.cv (nb095AlphaDummy670 x u D R S_cls f E)))).fv) :=
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
    (nb095AlphaDummy005 x u D R S_cls f E) ∈
      (((Class.cab (nb095AlphaDummy672 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095AlphaDummy670 x u D R S_cls f E)
              (synWbr (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))))
            (synCsn (Class.cv (nb095AlphaDummy672 x u D R S_cls f E)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
          (nb095AlphaDummy672 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy672;
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
        (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
            (nb095AlphaDummy670 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy670;
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
    (nb095AlphaDummy003 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy669 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0703 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy003 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy677 D R S_cls E)
              (synWrex (nb095AlphaDummy678 D R S_cls E)
                (Class.cv (nb095AlphaDummy003 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy677 D R S_cls E)
              (synWrex (nb095AlphaDummy678 D R S_cls E)
                (Class.cv (nb095AlphaDummy669 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy003 D R S_cls E) ≠ (nb095AlphaDummy677 D R S_cls E) from (by
          unfold nb095AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0702 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy003 D R S_cls E) ≠ (nb095AlphaDummy678 D R S_cls E) from (by
            unfold nb095AlphaDummy678;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0702 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0704 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy005 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy670 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0705 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy005 x u D R S_cls f E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E)) (synCphi
                    (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
          (nb095AlphaDummy679 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy679;
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
        (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
            (nb095AlphaDummy680 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy680;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0704 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0706 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy003 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy677 D R S_cls E)
            (synWrex (nb095AlphaDummy678 D R S_cls E)
              (Class.cv (nb095AlphaDummy003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy677 D R S_cls E)
            (synWrex (nb095AlphaDummy678 D R S_cls E)
              (Class.cv (nb095AlphaDummy003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy003 D R S_cls E) ≠ (nb095AlphaDummy677 D R S_cls E) from (by
          unfold nb095AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0702 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy003 D R S_cls E) ≠ (nb095AlphaDummy678 D R S_cls E) from (by
            unfold nb095AlphaDummy678;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0702 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0707 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy005 x u D R S_cls f E) ∈
      (((Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
          (nb095AlphaDummy679 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy679;
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
        (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
            (nb095AlphaDummy680 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy680;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0704 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0708 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy678 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy678 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0709 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy680 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy680 x u D R S_cls f E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0710 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy685 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy685 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy685 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy685 D R S_cls E))).fv) :=
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
    (nb095AlphaDummy687 x u D R S_cls f E) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy687 x u D R S_cls f E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy687 x u D R S_cls f E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv) :=
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
    (nb095AlphaDummy685 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy685 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0713 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy687 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0714 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy692 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy692 D R S_cls E))
            (Class.cv (nb095AlphaDummy693 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy692 D R S_cls E))
            (Class.cv (nb095AlphaDummy693 D R S_cls E)))).fv) :=
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
    (nb095AlphaDummy695 x u D R S_cls f E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy695 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy696 x u D R S_cls f E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy695 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy696 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0716 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy692 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy692 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy693 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0717 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy695 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy695 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy696 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0718 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy693 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy692 D R S_cls E))
            (Class.cv (nb095AlphaDummy693 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy692 D R S_cls E))
            (Class.cv (nb095AlphaDummy693 D R S_cls E)))).fv) :=
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
    (nb095AlphaDummy696 x u D R S_cls f E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy695 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy696 x u D R S_cls f E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy695 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy696 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0720 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy693 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy692 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy693 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0721 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy696 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy695 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy696 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0722 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy692 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy692 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy693 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0723 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy695 x u D R S_cls f E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy695 x u D R S_cls f E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy696 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0724 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy692 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy692 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy692 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
