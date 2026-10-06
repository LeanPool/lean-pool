/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part024`. -/


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

theorem nb078_support_mem_0313 (g : Var) :
    (nb078AlphaDummy314 g) ∈
      (((Class.cv (nb078AlphaDummy313 g))).fv ∪ ((Class.cv (nb078AlphaDummy314 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0314 :
    (nb078AlphaDummy310) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy310)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy311)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0315 (g : Var) :
    (nb078AlphaDummy313 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy313 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy314 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0316 :
    (nb078AlphaDummy310) ∈
      (((Class.cv (nb078AlphaDummy310))).fv ∪ ((Class.cv (nb078AlphaDummy310))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0317 (g : Var) :
    (nb078AlphaDummy313 g) ∈
      (((Class.cv (nb078AlphaDummy313 g))).fv ∪ ((Class.cv (nb078AlphaDummy313 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0318 :
    (nb078AlphaDummy311) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy310)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy311)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0319 (g : Var) :
    (nb078AlphaDummy314 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy313 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy314 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0320 :
    (nb078AlphaDummy311) ∈
      (((Class.cv (nb078AlphaDummy311))).fv ∪ ((Class.cv (nb078AlphaDummy311))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0321 (g : Var) :
    (nb078AlphaDummy314 g) ∈
      (((Class.cv (nb078AlphaDummy314 g))).fv ∪ ((Class.cv (nb078AlphaDummy314 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0322 :
    (nb078AlphaDummy288) ∈
      (((Class.cv (nb078AlphaDummy287))).fv ∪ ((Class.cv (nb078AlphaDummy288))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0323 :
    (nb078AlphaDummy288) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy295)
              (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy287))
                (Wff.classEq (Class.cv (nb078AlphaDummy295))
                  (synCphi (Class.cv (nb078AlphaDummy296)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy295)
              (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy288))
                (Wff.classEq (Class.cv (nb078AlphaDummy295))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy296)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy288) ≠ (nb078AlphaDummy295) from (by
          unfold nb078AlphaDummy295;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0322) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy288) ≠ (nb078AlphaDummy296) from (by
            unfold nb078AlphaDummy296;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0322) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0324 (g : Var) :
    (nb078AlphaDummy291 g) ∈
      (((Class.cv (nb078AlphaDummy290 g))).fv ∪ ((Class.cv (nb078AlphaDummy291 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0325 (g : Var) :
    (nb078AlphaDummy291 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy297 g)
              (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy290 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                  (synCphi (Class.cv (nb078AlphaDummy298 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy297 g)
              (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy291 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy298 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy291 g) ≠ (nb078AlphaDummy297 g) from (by
          unfold nb078AlphaDummy297;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0324 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy291 g) ≠ (nb078AlphaDummy298 g) from (by
            unfold nb078AlphaDummy298;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0324 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0326 :
    (nb078AlphaDummy288) ∈
      (((Class.cab (nb078AlphaDummy295)
            (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy288))
              (Wff.classEq (Class.cv (nb078AlphaDummy295))
                (synCun (synCphi (Class.cv (nb078AlphaDummy296)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy295)
            (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy288))
              (Wff.classEq (Class.cv (nb078AlphaDummy295))
                (synCun (synCphi (Class.cv (nb078AlphaDummy296)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy288) ≠ (nb078AlphaDummy295) from (by
          unfold nb078AlphaDummy295;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0322) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy288) ≠ (nb078AlphaDummy296) from (by
            unfold nb078AlphaDummy296;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0322) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0327 (g : Var) :
    (nb078AlphaDummy291 g) ∈
      (((Class.cab (nb078AlphaDummy297 g)
            (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy291 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy298 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy297 g)
            (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy291 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy298 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy291 g) ≠ (nb078AlphaDummy297 g) from (by
          unfold nb078AlphaDummy297;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0324 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy291 g) ≠ (nb078AlphaDummy298 g) from (by
            unfold nb078AlphaDummy298;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0324 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0328 :
    (nb078AlphaDummy296) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy296))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0329 (g : Var) :
    (nb078AlphaDummy298 g) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy298 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0330 :
    (nb078AlphaDummy296) ∈
      (((synCphi (Class.cv (nb078AlphaDummy296)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy296)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0331 (g : Var) :
    (nb078AlphaDummy298 g) ∈
      (((synCphi (Class.cv (nb078AlphaDummy298 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy298 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0332 :
    (nb078AlphaDummy287) ∈
      (((Class.cv (nb078AlphaDummy287))).fv ∪ ((Class.cv (nb078AlphaDummy289))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0333 :
    (nb078AlphaDummy287) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy331)
              (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy287))
                (Wff.classEq (Class.cv (nb078AlphaDummy331))
                  (synCphi (Class.cv (nb078AlphaDummy332)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy331)
              (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy289))
                (Wff.classEq (Class.cv (nb078AlphaDummy331))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy332)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy331) from (by
          unfold nb078AlphaDummy331;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0332) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy332) from (by
            unfold nb078AlphaDummy332;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0332) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0334 (g : Var) :
    (nb078AlphaDummy290 g) ∈
      (((Class.cv (nb078AlphaDummy290 g))).fv ∪ ((Class.cv (nb078AlphaDummy292 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0335 (g : Var) :
    (nb078AlphaDummy290 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy333 g)
              (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy290 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                  (synCphi (Class.cv (nb078AlphaDummy334 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy333 g)
              (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy292 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy334 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy333 g) from (by
          unfold nb078AlphaDummy333;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0334 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy334 g) from (by
            unfold nb078AlphaDummy334;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0334 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0336 :
    (nb078AlphaDummy287) ∈
      (((Class.cab (nb078AlphaDummy331)
            (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy287))
              (Wff.classEq (Class.cv (nb078AlphaDummy331))
                (synCphi (Class.cv (nb078AlphaDummy332))))))).fv ∪
        ((Class.cab (nb078AlphaDummy331)
            (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy287))
              (Wff.classEq (Class.cv (nb078AlphaDummy331))
                (synCphi (Class.cv (nb078AlphaDummy332))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy331) from (by
          unfold nb078AlphaDummy331;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0332) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy332) from (by
            unfold nb078AlphaDummy332;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0332) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0337 (g : Var) :
    (nb078AlphaDummy290 g) ∈
      (((Class.cab (nb078AlphaDummy333 g)
            (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy290 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                (synCphi (Class.cv (nb078AlphaDummy334 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy333 g)
            (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy290 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                (synCphi (Class.cv (nb078AlphaDummy334 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy333 g) from (by
          unfold nb078AlphaDummy333;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0334 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy334 g) from (by
            unfold nb078AlphaDummy334;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0334 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0338 :
    (nb078AlphaDummy332) ∈ (((Class.cv (nb078AlphaDummy332))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0339 (g : Var) :
    (nb078AlphaDummy334 g) ∈ (((Class.cv (nb078AlphaDummy334 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0340 :
    (nb078AlphaDummy339) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy339)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy339)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy339))).fv) :=
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

theorem nb078_support_mem_0341 (g : Var) :
    (nb078AlphaDummy341 g) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy341 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy341 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy341 g))).fv) :=
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

theorem nb078_support_mem_0342 :
    (nb078AlphaDummy339) ∈
      (((Class.cv (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0343 (g : Var) :
    (nb078AlphaDummy341 g) ∈
      (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0344 :
    (nb078AlphaDummy346) ∈
      (((synCnin (Class.cv (nb078AlphaDummy346)) (Class.cv (nb078AlphaDummy347)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy346))
            (Class.cv (nb078AlphaDummy347)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0345 (g : Var) :
    (nb078AlphaDummy349 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy349 g))
            (Class.cv (nb078AlphaDummy350 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy349 g))
            (Class.cv (nb078AlphaDummy350 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0346 :
    (nb078AlphaDummy346) ∈
      (((Class.cv (nb078AlphaDummy346))).fv ∪ ((Class.cv (nb078AlphaDummy347))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0347 (g : Var) :
    (nb078AlphaDummy349 g) ∈
      (((Class.cv (nb078AlphaDummy349 g))).fv ∪ ((Class.cv (nb078AlphaDummy350 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0348 :
    (nb078AlphaDummy347) ∈
      (((synCnin (Class.cv (nb078AlphaDummy346)) (Class.cv (nb078AlphaDummy347)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy346))
            (Class.cv (nb078AlphaDummy347)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0349 (g : Var) :
    (nb078AlphaDummy350 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy349 g))
            (Class.cv (nb078AlphaDummy350 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy349 g))
            (Class.cv (nb078AlphaDummy350 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0350 :
    (nb078AlphaDummy347) ∈
      (((Class.cv (nb078AlphaDummy346))).fv ∪ ((Class.cv (nb078AlphaDummy347))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0351 (g : Var) :
    (nb078AlphaDummy350 g) ∈
      (((Class.cv (nb078AlphaDummy349 g))).fv ∪ ((Class.cv (nb078AlphaDummy350 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0352 :
    (nb078AlphaDummy346) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy346)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy347)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0353 (g : Var) :
    (nb078AlphaDummy349 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy349 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy350 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0354 :
    (nb078AlphaDummy346) ∈
      (((Class.cv (nb078AlphaDummy346))).fv ∪ ((Class.cv (nb078AlphaDummy346))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0355 (g : Var) :
    (nb078AlphaDummy349 g) ∈
      (((Class.cv (nb078AlphaDummy349 g))).fv ∪ ((Class.cv (nb078AlphaDummy349 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0356 :
    (nb078AlphaDummy347) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy346)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy347)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0357 (g : Var) :
    (nb078AlphaDummy350 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy349 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy350 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0358 :
    (nb078AlphaDummy347) ∈
      (((Class.cv (nb078AlphaDummy347))).fv ∪ ((Class.cv (nb078AlphaDummy347))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0359 (g : Var) :
    (nb078AlphaDummy350 g) ∈
      (((Class.cv (nb078AlphaDummy350 g))).fv ∪ ((Class.cv (nb078AlphaDummy350 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0360 :
    (nb078AlphaDummy289) ∈
      (((Class.cv (nb078AlphaDummy287))).fv ∪ ((Class.cv (nb078AlphaDummy289))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0361 :
    (nb078AlphaDummy289) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy331)
              (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy287))
                (Wff.classEq (Class.cv (nb078AlphaDummy331))
                  (synCphi (Class.cv (nb078AlphaDummy332)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy331)
              (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy289))
                (Wff.classEq (Class.cv (nb078AlphaDummy331))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy332)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy331) from (by
          unfold nb078AlphaDummy331;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0360) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy332) from (by
            unfold nb078AlphaDummy332;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0360) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0362 (g : Var) :
    (nb078AlphaDummy292 g) ∈
      (((Class.cv (nb078AlphaDummy290 g))).fv ∪ ((Class.cv (nb078AlphaDummy292 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0363 (g : Var) :
    (nb078AlphaDummy292 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy333 g)
              (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy290 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                  (synCphi (Class.cv (nb078AlphaDummy334 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy333 g)
              (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy292 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy334 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy333 g) from (by
          unfold nb078AlphaDummy333;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0362 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy334 g) from (by
            unfold nb078AlphaDummy334;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0362 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0364 :
    (nb078AlphaDummy289) ∈
      (((Class.cab (nb078AlphaDummy331)
            (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy289))
              (Wff.classEq (Class.cv (nb078AlphaDummy331))
                (synCun (synCphi (Class.cv (nb078AlphaDummy332)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy331)
            (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy289))
              (Wff.classEq (Class.cv (nb078AlphaDummy331))
                (synCun (synCphi (Class.cv (nb078AlphaDummy332)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy331) from (by
          unfold nb078AlphaDummy331;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0360) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy332) from (by
            unfold nb078AlphaDummy332;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0360) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0365 (g : Var) :
    (nb078AlphaDummy292 g) ∈
      (((Class.cab (nb078AlphaDummy333 g)
            (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy292 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy334 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy333 g)
            (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy292 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy334 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy333 g) from (by
          unfold nb078AlphaDummy333;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0362 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy334 g) from (by
            unfold nb078AlphaDummy334;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0362 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0366 :
    (nb078AlphaDummy332) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy332))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0367 (g : Var) :
    (nb078AlphaDummy334 g) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy334 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0368 :
    (nb078AlphaDummy332) ∈
      (((synCphi (Class.cv (nb078AlphaDummy332)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy332)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0369 (g : Var) :
    (nb078AlphaDummy334 g) ∈
      (((synCphi (Class.cv (nb078AlphaDummy334 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy334 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0370 :
    (nb078AlphaDummy367) ∈
      (({(nb078AlphaDummy367)} : Finset Var) ∪ ({(nb078AlphaDummy368)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy368)) (Class.cv (nb078AlphaDummy001))
            (Class.cv (nb078AlphaDummy367)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0371 (g : Var) :
    (nb078AlphaDummy369 g) ∈
      (({(nb078AlphaDummy369 g)} : Finset Var) ∪ ({(nb078AlphaDummy370 g)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy370 g)) (Class.cv g)
            (Class.cv (nb078AlphaDummy369 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0372 :
    (nb078AlphaDummy368) ∈
      (({(nb078AlphaDummy367)} : Finset Var) ∪ ({(nb078AlphaDummy368)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy368)) (Class.cv (nb078AlphaDummy001))
            (Class.cv (nb078AlphaDummy367)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0373 (g : Var) :
    (nb078AlphaDummy370 g) ∈
      (({(nb078AlphaDummy369 g)} : Finset Var) ∪ ({(nb078AlphaDummy370 g)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy370 g)) (Class.cv g)
            (Class.cv (nb078AlphaDummy369 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0374 :
    (nb078AlphaDummy367) ∈
      (((Class.cv (nb078AlphaDummy367))).fv ∪ ((Class.cv (nb078AlphaDummy368))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0375 :
    (nb078AlphaDummy367) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy373)
              (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy367))
                (Wff.classEq (Class.cv (nb078AlphaDummy373))
                  (synCphi (Class.cv (nb078AlphaDummy374)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy373)
              (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy368))
                (Wff.classEq (Class.cv (nb078AlphaDummy373))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy374)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy373) from (by
          unfold nb078AlphaDummy373;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy374) from (by
            unfold nb078AlphaDummy374;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0376 (g : Var) :
    (nb078AlphaDummy369 g) ∈
      (((Class.cv (nb078AlphaDummy369 g))).fv ∪ ((Class.cv (nb078AlphaDummy370 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0377 (g : Var) :
    (nb078AlphaDummy369 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy375 g)
              (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy369 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                  (synCphi (Class.cv (nb078AlphaDummy376 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy375 g)
              (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy370 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy376 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy375 g) from (by
          unfold nb078AlphaDummy375;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0376 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy376 g) from (by
            unfold nb078AlphaDummy376;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0376 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0378 :
    (nb078AlphaDummy367) ∈
      (((Class.cab (nb078AlphaDummy373)
            (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy367))
              (Wff.classEq (Class.cv (nb078AlphaDummy373))
                (synCphi (Class.cv (nb078AlphaDummy374))))))).fv ∪
        ((Class.cab (nb078AlphaDummy373)
            (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy367))
              (Wff.classEq (Class.cv (nb078AlphaDummy373))
                (synCphi (Class.cv (nb078AlphaDummy374))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy373) from (by
          unfold nb078AlphaDummy373;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy374) from (by
            unfold nb078AlphaDummy374;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0379 (g : Var) :
    (nb078AlphaDummy369 g) ∈
      (((Class.cab (nb078AlphaDummy375 g)
            (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy369 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                (synCphi (Class.cv (nb078AlphaDummy376 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy375 g)
            (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy369 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                (synCphi (Class.cv (nb078AlphaDummy376 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy375 g) from (by
          unfold nb078AlphaDummy375;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0376 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy376 g) from (by
            unfold nb078AlphaDummy376;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0376 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0380 :
    (nb078AlphaDummy374) ∈ (((Class.cv (nb078AlphaDummy374))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0381 (g : Var) :
    (nb078AlphaDummy376 g) ∈ (((Class.cv (nb078AlphaDummy376 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0382 :
    (nb078AlphaDummy381) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy381)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy381)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy381))).fv) :=
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

theorem nb078_support_mem_0383 (g : Var) :
    (nb078AlphaDummy383 g) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy383 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy383 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy383 g))).fv) :=
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

theorem nb078_support_mem_0384 :
    (nb078AlphaDummy381) ∈
      (((Class.cv (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0385 (g : Var) :
    (nb078AlphaDummy383 g) ∈
      (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0386 :
    (nb078AlphaDummy388) ∈
      (((synCnin (Class.cv (nb078AlphaDummy388)) (Class.cv (nb078AlphaDummy389)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy388))
            (Class.cv (nb078AlphaDummy389)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0387 (g : Var) :
    (nb078AlphaDummy391 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy391 g))
            (Class.cv (nb078AlphaDummy392 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy391 g))
            (Class.cv (nb078AlphaDummy392 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0388 :
    (nb078AlphaDummy388) ∈
      (((Class.cv (nb078AlphaDummy388))).fv ∪ ((Class.cv (nb078AlphaDummy389))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0389 (g : Var) :
    (nb078AlphaDummy391 g) ∈
      (((Class.cv (nb078AlphaDummy391 g))).fv ∪ ((Class.cv (nb078AlphaDummy392 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0390 :
    (nb078AlphaDummy389) ∈
      (((synCnin (Class.cv (nb078AlphaDummy388)) (Class.cv (nb078AlphaDummy389)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy388))
            (Class.cv (nb078AlphaDummy389)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0391 (g : Var) :
    (nb078AlphaDummy392 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy391 g))
            (Class.cv (nb078AlphaDummy392 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy391 g))
            (Class.cv (nb078AlphaDummy392 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0392 :
    (nb078AlphaDummy389) ∈
      (((Class.cv (nb078AlphaDummy388))).fv ∪ ((Class.cv (nb078AlphaDummy389))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0393 (g : Var) :
    (nb078AlphaDummy392 g) ∈
      (((Class.cv (nb078AlphaDummy391 g))).fv ∪ ((Class.cv (nb078AlphaDummy392 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0394 :
    (nb078AlphaDummy388) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy388)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy389)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0395 (g : Var) :
    (nb078AlphaDummy391 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy391 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy392 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0396 :
    (nb078AlphaDummy388) ∈
      (((Class.cv (nb078AlphaDummy388))).fv ∪ ((Class.cv (nb078AlphaDummy388))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0397 (g : Var) :
    (nb078AlphaDummy391 g) ∈
      (((Class.cv (nb078AlphaDummy391 g))).fv ∪ ((Class.cv (nb078AlphaDummy391 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0398 :
    (nb078AlphaDummy389) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy388)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy389)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0399 (g : Var) :
    (nb078AlphaDummy392 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy391 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy392 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0400 :
    (nb078AlphaDummy389) ∈
      (((Class.cv (nb078AlphaDummy389))).fv ∪ ((Class.cv (nb078AlphaDummy389))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0401 (g : Var) :
    (nb078AlphaDummy392 g) ∈
      (((Class.cv (nb078AlphaDummy392 g))).fv ∪ ((Class.cv (nb078AlphaDummy392 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0402 :
    (nb078AlphaDummy368) ∈
      (((Class.cv (nb078AlphaDummy367))).fv ∪ ((Class.cv (nb078AlphaDummy368))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0403 :
    (nb078AlphaDummy368) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy373)
              (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy367))
                (Wff.classEq (Class.cv (nb078AlphaDummy373))
                  (synCphi (Class.cv (nb078AlphaDummy374)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy373)
              (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy368))
                (Wff.classEq (Class.cv (nb078AlphaDummy373))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy374)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy373) from (by
          unfold nb078AlphaDummy373;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0402) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy374) from (by
            unfold nb078AlphaDummy374;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0402) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0404 (g : Var) :
    (nb078AlphaDummy370 g) ∈
      (((Class.cv (nb078AlphaDummy369 g))).fv ∪ ((Class.cv (nb078AlphaDummy370 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0405 (g : Var) :
    (nb078AlphaDummy370 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy375 g)
              (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy369 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                  (synCphi (Class.cv (nb078AlphaDummy376 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy375 g)
              (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy370 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy376 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy375 g) from (by
          unfold nb078AlphaDummy375;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0404 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy376 g) from (by
            unfold nb078AlphaDummy376;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0404 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0406 :
    (nb078AlphaDummy368) ∈
      (((Class.cab (nb078AlphaDummy373)
            (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy368))
              (Wff.classEq (Class.cv (nb078AlphaDummy373))
                (synCun (synCphi (Class.cv (nb078AlphaDummy374)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy373)
            (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy368))
              (Wff.classEq (Class.cv (nb078AlphaDummy373))
                (synCun (synCphi (Class.cv (nb078AlphaDummy374)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy373) from (by
          unfold nb078AlphaDummy373;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0402) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy374) from (by
            unfold nb078AlphaDummy374;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0402) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0407 (g : Var) :
    (nb078AlphaDummy370 g) ∈
      (((Class.cab (nb078AlphaDummy375 g)
            (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy370 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy376 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy375 g)
            (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy370 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy376 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy375 g) from (by
          unfold nb078AlphaDummy375;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0404 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy376 g) from (by
            unfold nb078AlphaDummy376;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0404 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0408 :
    (nb078AlphaDummy374) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy374))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0409 (g : Var) :
    (nb078AlphaDummy376 g) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy376 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0410 :
    (nb078AlphaDummy374) ∈
      (((synCphi (Class.cv (nb078AlphaDummy374)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy374)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0411 (g : Var) :
    (nb078AlphaDummy376 g) ∈
      (((synCphi (Class.cv (nb078AlphaDummy376 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy376 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0412 :
    (nb078AlphaDummy368) ∈
      (((Class.cv (nb078AlphaDummy368))).fv ∪ ((Class.cv (nb078AlphaDummy367))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0413 :
    (nb078AlphaDummy368) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy409)
              (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy368))
                (Wff.classEq (Class.cv (nb078AlphaDummy409))
                  (synCphi (Class.cv (nb078AlphaDummy410)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy409)
              (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy367))
                (Wff.classEq (Class.cv (nb078AlphaDummy409))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy410)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy409) from (by
          unfold nb078AlphaDummy409;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy410) from (by
            unfold nb078AlphaDummy410;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0414 (g : Var) :
    (nb078AlphaDummy370 g) ∈
      (((Class.cv (nb078AlphaDummy370 g))).fv ∪ ((Class.cv (nb078AlphaDummy369 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0415 (g : Var) :
    (nb078AlphaDummy370 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy411 g)
              (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy370 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                  (synCphi (Class.cv (nb078AlphaDummy412 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy411 g)
              (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy369 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy412 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy411 g) from (by
          unfold nb078AlphaDummy411;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0414 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy412 g) from (by
            unfold nb078AlphaDummy412;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0414 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0416 :
    (nb078AlphaDummy368) ∈
      (((Class.cab (nb078AlphaDummy409)
            (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy368))
              (Wff.classEq (Class.cv (nb078AlphaDummy409))
                (synCphi (Class.cv (nb078AlphaDummy410))))))).fv ∪
        ((Class.cab (nb078AlphaDummy409)
            (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy368))
              (Wff.classEq (Class.cv (nb078AlphaDummy409))
                (synCphi (Class.cv (nb078AlphaDummy410))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy409) from (by
          unfold nb078AlphaDummy409;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy410) from (by
            unfold nb078AlphaDummy410;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0417 (g : Var) :
    (nb078AlphaDummy370 g) ∈
      (((Class.cab (nb078AlphaDummy411 g)
            (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy370 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                (synCphi (Class.cv (nb078AlphaDummy412 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy411 g)
            (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy370 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                (synCphi (Class.cv (nb078AlphaDummy412 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy411 g) from (by
          unfold nb078AlphaDummy411;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0414 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy412 g) from (by
            unfold nb078AlphaDummy412;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0414 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0418 :
    (nb078AlphaDummy410) ∈ (((Class.cv (nb078AlphaDummy410))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0419 (g : Var) :
    (nb078AlphaDummy412 g) ∈ (((Class.cv (nb078AlphaDummy412 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0420 :
    (nb078AlphaDummy417) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy417)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy417)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy417))).fv) :=
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

theorem nb078_support_mem_0421 (g : Var) :
    (nb078AlphaDummy419 g) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy419 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy419 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy419 g))).fv) :=
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

theorem nb078_support_mem_0422 :
    (nb078AlphaDummy417) ∈
      (((Class.cv (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0423 (g : Var) :
    (nb078AlphaDummy419 g) ∈
      (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0424 :
    (nb078AlphaDummy424) ∈
      (((synCnin (Class.cv (nb078AlphaDummy424)) (Class.cv (nb078AlphaDummy425)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy424))
            (Class.cv (nb078AlphaDummy425)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0425 (g : Var) :
    (nb078AlphaDummy427 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy427 g))
            (Class.cv (nb078AlphaDummy428 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy427 g))
            (Class.cv (nb078AlphaDummy428 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0426 :
    (nb078AlphaDummy424) ∈
      (((Class.cv (nb078AlphaDummy424))).fv ∪ ((Class.cv (nb078AlphaDummy425))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0427 (g : Var) :
    (nb078AlphaDummy427 g) ∈
      (((Class.cv (nb078AlphaDummy427 g))).fv ∪ ((Class.cv (nb078AlphaDummy428 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0428 :
    (nb078AlphaDummy425) ∈
      (((synCnin (Class.cv (nb078AlphaDummy424)) (Class.cv (nb078AlphaDummy425)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy424))
            (Class.cv (nb078AlphaDummy425)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0429 (g : Var) :
    (nb078AlphaDummy428 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy427 g))
            (Class.cv (nb078AlphaDummy428 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy427 g))
            (Class.cv (nb078AlphaDummy428 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0430 :
    (nb078AlphaDummy425) ∈
      (((Class.cv (nb078AlphaDummy424))).fv ∪ ((Class.cv (nb078AlphaDummy425))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0431 (g : Var) :
    (nb078AlphaDummy428 g) ∈
      (((Class.cv (nb078AlphaDummy427 g))).fv ∪ ((Class.cv (nb078AlphaDummy428 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0432 :
    (nb078AlphaDummy424) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy424)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy425)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0433 (g : Var) :
    (nb078AlphaDummy427 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy427 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy428 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0434 :
    (nb078AlphaDummy424) ∈
      (((Class.cv (nb078AlphaDummy424))).fv ∪ ((Class.cv (nb078AlphaDummy424))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0435 (g : Var) :
    (nb078AlphaDummy427 g) ∈
      (((Class.cv (nb078AlphaDummy427 g))).fv ∪ ((Class.cv (nb078AlphaDummy427 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0436 :
    (nb078AlphaDummy425) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy424)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy425)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0437 (g : Var) :
    (nb078AlphaDummy428 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy427 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy428 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0438 :
    (nb078AlphaDummy425) ∈
      (((Class.cv (nb078AlphaDummy425))).fv ∪ ((Class.cv (nb078AlphaDummy425))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0439 (g : Var) :
    (nb078AlphaDummy428 g) ∈
      (((Class.cv (nb078AlphaDummy428 g))).fv ∪ ((Class.cv (nb078AlphaDummy428 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0440 :
    (nb078AlphaDummy367) ∈
      (((Class.cv (nb078AlphaDummy368))).fv ∪ ((Class.cv (nb078AlphaDummy367))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0441 :
    (nb078AlphaDummy367) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy409)
              (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy368))
                (Wff.classEq (Class.cv (nb078AlphaDummy409))
                  (synCphi (Class.cv (nb078AlphaDummy410)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy409)
              (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy367))
                (Wff.classEq (Class.cv (nb078AlphaDummy409))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy410)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy409) from (by
          unfold nb078AlphaDummy409;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0440) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy410) from (by
            unfold nb078AlphaDummy410;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0440) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0442 (g : Var) :
    (nb078AlphaDummy369 g) ∈
      (((Class.cv (nb078AlphaDummy370 g))).fv ∪ ((Class.cv (nb078AlphaDummy369 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0443 (g : Var) :
    (nb078AlphaDummy369 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy411 g)
              (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy370 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                  (synCphi (Class.cv (nb078AlphaDummy412 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy411 g)
              (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy369 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy412 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy411 g) from (by
          unfold nb078AlphaDummy411;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0442 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy412 g) from (by
            unfold nb078AlphaDummy412;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0442 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0444 :
    (nb078AlphaDummy367) ∈
      (((Class.cab (nb078AlphaDummy409)
            (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy367))
              (Wff.classEq (Class.cv (nb078AlphaDummy409))
                (synCun (synCphi (Class.cv (nb078AlphaDummy410)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy409)
            (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy367))
              (Wff.classEq (Class.cv (nb078AlphaDummy409))
                (synCun (synCphi (Class.cv (nb078AlphaDummy410)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy409) from (by
          unfold nb078AlphaDummy409;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0440) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy410) from (by
            unfold nb078AlphaDummy410;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0440) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0445 (g : Var) :
    (nb078AlphaDummy369 g) ∈
      (((Class.cab (nb078AlphaDummy411 g)
            (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy369 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy412 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy411 g)
            (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy369 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy412 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy411 g) from (by
          unfold nb078AlphaDummy411;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0442 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy412 g) from (by
            unfold nb078AlphaDummy412;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0442 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0446 :
    (nb078AlphaDummy410) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy410))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0447 (g : Var) :
    (nb078AlphaDummy412 g) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy412 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0448 :
    (nb078AlphaDummy410) ∈
      (((synCphi (Class.cv (nb078AlphaDummy410)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy410)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0449 (g : Var) :
    (nb078AlphaDummy412 g) ∈
      (((synCphi (Class.cv (nb078AlphaDummy412 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy412 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0450 :
    (nb078AlphaDummy001) ∈
      (((synCnin (synCcom (Class.cv (nb078AlphaDummy001))
              (synCcnv (Class.cv (nb078AlphaDummy001)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb078AlphaDummy001))
              (synCcnv (Class.cv (nb078AlphaDummy001)))) (synCid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0451 (g : Var) :
    g ∈
      (((synCnin (synCcom (Class.cv g) (synCcnv (Class.cv g))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv g) (synCcnv (Class.cv g))) (synCid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0452 :
    (nb078AlphaDummy001) ∈
      (((synCcom (Class.cv (nb078AlphaDummy001))
            (synCcnv (Class.cv (nb078AlphaDummy001))))).fv ∪ ((synCid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0453 (g : Var) :
    g ∈ (((synCcom (Class.cv g) (synCcnv (Class.cv g)))).fv ∪ ((synCid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0454 :
    (nb078AlphaDummy001) ∈
      (((Class.cv (nb078AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part025`. -/


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

theorem nb078_support_mem_0455 :
    (nb078AlphaDummy001) ∈
      (({(nb078AlphaDummy287)} : Finset Var) ∪ ({(nb078AlphaDummy288)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy289) (synWa (synWbr (Class.cv (nb078AlphaDummy287))
                (synCcnv (Class.cv (nb078AlphaDummy001)))
                (Class.cv (nb078AlphaDummy289))) (synWbr (Class.cv (nb078AlphaDummy289))
                (Class.cv (nb078AlphaDummy001)) (Class.cv (nb078AlphaDummy288)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy289) from (by
          unfold nb078AlphaDummy289;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0454) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb078_support_mem_0456 (g : Var) :
    g ∈ (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0457 (g : Var) :
    g ∈
      (({(nb078AlphaDummy290 g)} : Finset Var) ∪ ({(nb078AlphaDummy291 g)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy292 g) (synWa
              (synWbr (Class.cv (nb078AlphaDummy290 g)) (synCcnv (Class.cv g))
                (Class.cv (nb078AlphaDummy292 g)))
              (synWbr (Class.cv (nb078AlphaDummy292 g)) (Class.cv g)
                (Class.cv (nb078AlphaDummy291 g)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show g ≠ (nb078AlphaDummy292 g) from (by
          unfold nb078AlphaDummy292;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0456 g) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb078_support_mem_0458 :
    (nb078AlphaDummy001) ∈
      (({(nb078AlphaDummy367)} : Finset Var) ∪ ({(nb078AlphaDummy368)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy368)) (Class.cv (nb078AlphaDummy001))
            (Class.cv (nb078AlphaDummy367)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0459 (g : Var) :
    g ∈
      (({(nb078AlphaDummy369 g)} : Finset Var) ∪ ({(nb078AlphaDummy370 g)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy370 g)) (Class.cv g)
            (Class.cv (nb078AlphaDummy369 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0460 :
    (nb078AlphaDummy001) ∈ (((Class.cv (nb078AlphaDummy001))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0461 (g : Var) : g ∈ (((Class.cv g)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0462 :
    (nb078AlphaDummy289) ∈
      (((Class.cv (nb078AlphaDummy289))).fv ∪ ((Class.cv (nb078AlphaDummy288))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0463 :
    (nb078AlphaDummy289) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy445)
              (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy289))
                (Wff.classEq (Class.cv (nb078AlphaDummy445))
                  (synCphi (Class.cv (nb078AlphaDummy446)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy445)
              (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy288))
                (Wff.classEq (Class.cv (nb078AlphaDummy445))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy446)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy445) from (by
          unfold nb078AlphaDummy445;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0462) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy446) from (by
            unfold nb078AlphaDummy446;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0462) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0464 (g : Var) :
    (nb078AlphaDummy292 g) ∈
      (((Class.cv (nb078AlphaDummy292 g))).fv ∪ ((Class.cv (nb078AlphaDummy291 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0465 (g : Var) :
    (nb078AlphaDummy292 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy447 g)
              (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy292 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                  (synCphi (Class.cv (nb078AlphaDummy448 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy447 g)
              (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy291 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy448 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy447 g) from (by
          unfold nb078AlphaDummy447;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0464 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy448 g) from (by
            unfold nb078AlphaDummy448;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0464 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0466 :
    (nb078AlphaDummy289) ∈
      (((Class.cab (nb078AlphaDummy445)
            (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy289))
              (Wff.classEq (Class.cv (nb078AlphaDummy445))
                (synCphi (Class.cv (nb078AlphaDummy446))))))).fv ∪
        ((Class.cab (nb078AlphaDummy445)
            (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy289))
              (Wff.classEq (Class.cv (nb078AlphaDummy445))
                (synCphi (Class.cv (nb078AlphaDummy446))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy445) from (by
          unfold nb078AlphaDummy445;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0462) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy446) from (by
            unfold nb078AlphaDummy446;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0462) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0467 (g : Var) :
    (nb078AlphaDummy292 g) ∈
      (((Class.cab (nb078AlphaDummy447 g)
            (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy292 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                (synCphi (Class.cv (nb078AlphaDummy448 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy447 g)
            (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy292 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                (synCphi (Class.cv (nb078AlphaDummy448 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy447 g) from (by
          unfold nb078AlphaDummy447;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0464 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy448 g) from (by
            unfold nb078AlphaDummy448;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0464 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0468 :
    (nb078AlphaDummy446) ∈ (((Class.cv (nb078AlphaDummy446))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0469 (g : Var) :
    (nb078AlphaDummy448 g) ∈ (((Class.cv (nb078AlphaDummy448 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0470 :
    (nb078AlphaDummy453) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy453)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy453)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy453))).fv) :=
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

theorem nb078_support_mem_0471 (g : Var) :
    (nb078AlphaDummy455 g) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy455 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy455 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy455 g))).fv) :=
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

theorem nb078_support_mem_0472 :
    (nb078AlphaDummy453) ∈
      (((Class.cv (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0473 (g : Var) :
    (nb078AlphaDummy455 g) ∈
      (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0474 :
    (nb078AlphaDummy460) ∈
      (((synCnin (Class.cv (nb078AlphaDummy460)) (Class.cv (nb078AlphaDummy461)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy460))
            (Class.cv (nb078AlphaDummy461)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0475 (g : Var) :
    (nb078AlphaDummy463 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy463 g))
            (Class.cv (nb078AlphaDummy464 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy463 g))
            (Class.cv (nb078AlphaDummy464 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0476 :
    (nb078AlphaDummy460) ∈
      (((Class.cv (nb078AlphaDummy460))).fv ∪ ((Class.cv (nb078AlphaDummy461))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0477 (g : Var) :
    (nb078AlphaDummy463 g) ∈
      (((Class.cv (nb078AlphaDummy463 g))).fv ∪ ((Class.cv (nb078AlphaDummy464 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0478 :
    (nb078AlphaDummy461) ∈
      (((synCnin (Class.cv (nb078AlphaDummy460)) (Class.cv (nb078AlphaDummy461)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy460))
            (Class.cv (nb078AlphaDummy461)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0479 (g : Var) :
    (nb078AlphaDummy464 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy463 g))
            (Class.cv (nb078AlphaDummy464 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy463 g))
            (Class.cv (nb078AlphaDummy464 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0480 :
    (nb078AlphaDummy461) ∈
      (((Class.cv (nb078AlphaDummy460))).fv ∪ ((Class.cv (nb078AlphaDummy461))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0481 (g : Var) :
    (nb078AlphaDummy464 g) ∈
      (((Class.cv (nb078AlphaDummy463 g))).fv ∪ ((Class.cv (nb078AlphaDummy464 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0482 :
    (nb078AlphaDummy460) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy460)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy461)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0483 (g : Var) :
    (nb078AlphaDummy463 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy463 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy464 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0484 :
    (nb078AlphaDummy460) ∈
      (((Class.cv (nb078AlphaDummy460))).fv ∪ ((Class.cv (nb078AlphaDummy460))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0485 (g : Var) :
    (nb078AlphaDummy463 g) ∈
      (((Class.cv (nb078AlphaDummy463 g))).fv ∪ ((Class.cv (nb078AlphaDummy463 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0486 :
    (nb078AlphaDummy461) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy460)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy461)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0487 (g : Var) :
    (nb078AlphaDummy464 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy463 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy464 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0488 :
    (nb078AlphaDummy461) ∈
      (((Class.cv (nb078AlphaDummy461))).fv ∪ ((Class.cv (nb078AlphaDummy461))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0489 (g : Var) :
    (nb078AlphaDummy464 g) ∈
      (((Class.cv (nb078AlphaDummy464 g))).fv ∪ ((Class.cv (nb078AlphaDummy464 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0490 :
    (nb078AlphaDummy288) ∈
      (((Class.cv (nb078AlphaDummy289))).fv ∪ ((Class.cv (nb078AlphaDummy288))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0491 :
    (nb078AlphaDummy288) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy445)
              (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy289))
                (Wff.classEq (Class.cv (nb078AlphaDummy445))
                  (synCphi (Class.cv (nb078AlphaDummy446)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy445)
              (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy288))
                (Wff.classEq (Class.cv (nb078AlphaDummy445))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy446)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy288) ≠ (nb078AlphaDummy445) from (by
          unfold nb078AlphaDummy445;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0490) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy288) ≠ (nb078AlphaDummy446) from (by
            unfold nb078AlphaDummy446;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0490) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0492 (g : Var) :
    (nb078AlphaDummy291 g) ∈
      (((Class.cv (nb078AlphaDummy292 g))).fv ∪ ((Class.cv (nb078AlphaDummy291 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0493 (g : Var) :
    (nb078AlphaDummy291 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy447 g)
              (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy292 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                  (synCphi (Class.cv (nb078AlphaDummy448 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy447 g)
              (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy291 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy448 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy291 g) ≠ (nb078AlphaDummy447 g) from (by
          unfold nb078AlphaDummy447;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0492 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy291 g) ≠ (nb078AlphaDummy448 g) from (by
            unfold nb078AlphaDummy448;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0492 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0494 :
    (nb078AlphaDummy288) ∈
      (((Class.cab (nb078AlphaDummy445)
            (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy288))
              (Wff.classEq (Class.cv (nb078AlphaDummy445))
                (synCun (synCphi (Class.cv (nb078AlphaDummy446)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy445)
            (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy288))
              (Wff.classEq (Class.cv (nb078AlphaDummy445))
                (synCun (synCphi (Class.cv (nb078AlphaDummy446)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy288) ≠ (nb078AlphaDummy445) from (by
          unfold nb078AlphaDummy445;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0490) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy288) ≠ (nb078AlphaDummy446) from (by
            unfold nb078AlphaDummy446;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0490) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0495 (g : Var) :
    (nb078AlphaDummy291 g) ∈
      (((Class.cab (nb078AlphaDummy447 g)
            (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy291 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy448 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy447 g)
            (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy291 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy448 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy291 g) ≠ (nb078AlphaDummy447 g) from (by
          unfold nb078AlphaDummy447;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0492 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy291 g) ≠ (nb078AlphaDummy448 g) from (by
            unfold nb078AlphaDummy448;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0492 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0496 :
    (nb078AlphaDummy446) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy446))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0497 (g : Var) :
    (nb078AlphaDummy448 g) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy448 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0498 :
    (nb078AlphaDummy446) ∈
      (((synCphi (Class.cv (nb078AlphaDummy446)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy446)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0499 (g : Var) :
    (nb078AlphaDummy448 g) ∈
      (((synCphi (Class.cv (nb078AlphaDummy448 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy448 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0500 :
    (nb078AlphaDummy482) ∈
      (((Class.cv (nb078AlphaDummy482))).fv ∪ ((Class.cv (nb078AlphaDummy481))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0501 :
    (nb078AlphaDummy482) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy485)
              (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy482))
                (Wff.classEq (Class.cv (nb078AlphaDummy485))
                  (synCphi (Class.cv (nb078AlphaDummy486)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy485)
              (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy481))
                (Wff.classEq (Class.cv (nb078AlphaDummy485))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy486)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy482) ≠ (nb078AlphaDummy485) from (by
          unfold nb078AlphaDummy485;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0500) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy482) ≠ (nb078AlphaDummy486) from (by
            unfold nb078AlphaDummy486;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0500) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0502 (g : Var) :
    (nb078AlphaDummy484 g) ∈
      (((Class.cv (nb078AlphaDummy484 g))).fv ∪ ((Class.cv (nb078AlphaDummy483 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0503 (g : Var) :
    (nb078AlphaDummy484 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy487 g)
              (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy484 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                  (synCphi (Class.cv (nb078AlphaDummy488 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy487 g)
              (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy483 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy488 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy484 g) ≠ (nb078AlphaDummy487 g) from (by
          unfold nb078AlphaDummy487;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0502 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy484 g) ≠ (nb078AlphaDummy488 g) from (by
            unfold nb078AlphaDummy488;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0502 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0504 :
    (nb078AlphaDummy482) ∈
      (((Class.cab (nb078AlphaDummy485)
            (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy482))
              (Wff.classEq (Class.cv (nb078AlphaDummy485))
                (synCphi (Class.cv (nb078AlphaDummy486))))))).fv ∪
        ((Class.cab (nb078AlphaDummy485)
            (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy482))
              (Wff.classEq (Class.cv (nb078AlphaDummy485))
                (synCphi (Class.cv (nb078AlphaDummy486))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy482) ≠ (nb078AlphaDummy485) from (by
          unfold nb078AlphaDummy485;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0500) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy482) ≠ (nb078AlphaDummy486) from (by
            unfold nb078AlphaDummy486;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0500) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0505 (g : Var) :
    (nb078AlphaDummy484 g) ∈
      (((Class.cab (nb078AlphaDummy487 g)
            (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy484 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                (synCphi (Class.cv (nb078AlphaDummy488 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy487 g)
            (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy484 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                (synCphi (Class.cv (nb078AlphaDummy488 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy484 g) ≠ (nb078AlphaDummy487 g) from (by
          unfold nb078AlphaDummy487;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0502 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy484 g) ≠ (nb078AlphaDummy488 g) from (by
            unfold nb078AlphaDummy488;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0502 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0506 :
    (nb078AlphaDummy486) ∈ (((Class.cv (nb078AlphaDummy486))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0507 (g : Var) :
    (nb078AlphaDummy488 g) ∈ (((Class.cv (nb078AlphaDummy488 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0508 :
    (nb078AlphaDummy493) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy493)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy493)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy493))).fv) :=
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

theorem nb078_support_mem_0509 (g : Var) :
    (nb078AlphaDummy495 g) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy495 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy495 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy495 g))).fv) :=
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

theorem nb078_support_mem_0510 :
    (nb078AlphaDummy493) ∈
      (((Class.cv (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0511 (g : Var) :
    (nb078AlphaDummy495 g) ∈
      (((Class.cv (nb078AlphaDummy495 g))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0512 :
    (nb078AlphaDummy500) ∈
      (((synCnin (Class.cv (nb078AlphaDummy500)) (Class.cv (nb078AlphaDummy501)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy500))
            (Class.cv (nb078AlphaDummy501)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0513 (g : Var) :
    (nb078AlphaDummy503 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy503 g))
            (Class.cv (nb078AlphaDummy504 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy503 g))
            (Class.cv (nb078AlphaDummy504 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0514 :
    (nb078AlphaDummy500) ∈
      (((Class.cv (nb078AlphaDummy500))).fv ∪ ((Class.cv (nb078AlphaDummy501))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0515 (g : Var) :
    (nb078AlphaDummy503 g) ∈
      (((Class.cv (nb078AlphaDummy503 g))).fv ∪ ((Class.cv (nb078AlphaDummy504 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0516 :
    (nb078AlphaDummy501) ∈
      (((synCnin (Class.cv (nb078AlphaDummy500)) (Class.cv (nb078AlphaDummy501)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy500))
            (Class.cv (nb078AlphaDummy501)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0517 (g : Var) :
    (nb078AlphaDummy504 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy503 g))
            (Class.cv (nb078AlphaDummy504 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy503 g))
            (Class.cv (nb078AlphaDummy504 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0518 :
    (nb078AlphaDummy501) ∈
      (((Class.cv (nb078AlphaDummy500))).fv ∪ ((Class.cv (nb078AlphaDummy501))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0519 (g : Var) :
    (nb078AlphaDummy504 g) ∈
      (((Class.cv (nb078AlphaDummy503 g))).fv ∪ ((Class.cv (nb078AlphaDummy504 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0520 :
    (nb078AlphaDummy500) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy500)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy501)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0521 (g : Var) :
    (nb078AlphaDummy503 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy503 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy504 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0522 :
    (nb078AlphaDummy500) ∈
      (((Class.cv (nb078AlphaDummy500))).fv ∪ ((Class.cv (nb078AlphaDummy500))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0523 (g : Var) :
    (nb078AlphaDummy503 g) ∈
      (((Class.cv (nb078AlphaDummy503 g))).fv ∪ ((Class.cv (nb078AlphaDummy503 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0524 :
    (nb078AlphaDummy501) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy500)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy501)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0525 (g : Var) :
    (nb078AlphaDummy504 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy503 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy504 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0526 :
    (nb078AlphaDummy501) ∈
      (((Class.cv (nb078AlphaDummy501))).fv ∪ ((Class.cv (nb078AlphaDummy501))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0527 (g : Var) :
    (nb078AlphaDummy504 g) ∈
      (((Class.cv (nb078AlphaDummy504 g))).fv ∪ ((Class.cv (nb078AlphaDummy504 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0528 :
    (nb078AlphaDummy481) ∈
      (((Class.cv (nb078AlphaDummy482))).fv ∪ ((Class.cv (nb078AlphaDummy481))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0529 :
    (nb078AlphaDummy481) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy485)
              (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy482))
                (Wff.classEq (Class.cv (nb078AlphaDummy485))
                  (synCphi (Class.cv (nb078AlphaDummy486)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy485)
              (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy481))
                (Wff.classEq (Class.cv (nb078AlphaDummy485))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy486)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy481) ≠ (nb078AlphaDummy485) from (by
          unfold nb078AlphaDummy485;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0528) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy481) ≠ (nb078AlphaDummy486) from (by
            unfold nb078AlphaDummy486;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0528) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0530 (g : Var) :
    (nb078AlphaDummy483 g) ∈
      (((Class.cv (nb078AlphaDummy484 g))).fv ∪ ((Class.cv (nb078AlphaDummy483 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0531 (g : Var) :
    (nb078AlphaDummy483 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy487 g)
              (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy484 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                  (synCphi (Class.cv (nb078AlphaDummy488 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy487 g)
              (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy483 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy488 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy483 g) ≠ (nb078AlphaDummy487 g) from (by
          unfold nb078AlphaDummy487;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0530 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy483 g) ≠ (nb078AlphaDummy488 g) from (by
            unfold nb078AlphaDummy488;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0530 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0532 :
    (nb078AlphaDummy481) ∈
      (((Class.cab (nb078AlphaDummy485)
            (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy481))
              (Wff.classEq (Class.cv (nb078AlphaDummy485))
                (synCun (synCphi (Class.cv (nb078AlphaDummy486)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy485)
            (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy481))
              (Wff.classEq (Class.cv (nb078AlphaDummy485))
                (synCun (synCphi (Class.cv (nb078AlphaDummy486)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy481) ≠ (nb078AlphaDummy485) from (by
          unfold nb078AlphaDummy485;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0528) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy481) ≠ (nb078AlphaDummy486) from (by
            unfold nb078AlphaDummy486;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0528) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0533 (g : Var) :
    (nb078AlphaDummy483 g) ∈
      (((Class.cab (nb078AlphaDummy487 g)
            (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy483 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy488 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy487 g)
            (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy483 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy488 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy483 g) ≠ (nb078AlphaDummy487 g) from (by
          unfold nb078AlphaDummy487;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0530 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy483 g) ≠ (nb078AlphaDummy488 g) from (by
            unfold nb078AlphaDummy488;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0530 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0534 :
    (nb078AlphaDummy486) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy486))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0535 (g : Var) :
    (nb078AlphaDummy488 g) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy488 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0536 :
    (nb078AlphaDummy486) ∈
      (((synCphi (Class.cv (nb078AlphaDummy486)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy486)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0537 (g : Var) :
    (nb078AlphaDummy488 g) ∈
      (((synCphi (Class.cv (nb078AlphaDummy488 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy488 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0538 :
    (nb078AlphaDummy001) ∈
      (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0539 (g : Var) :
    g ∈ (((synCcnv (Class.cv g))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0540 :
    (nb078AlphaDummy526) ∈
      (((Class.cv (nb078AlphaDummy526))).fv ∪ ((Class.cv (nb078AlphaDummy525))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0541 :
    (nb078AlphaDummy526) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy529)
              (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy526))
                (Wff.classEq (Class.cv (nb078AlphaDummy529))
                  (synCphi (Class.cv (nb078AlphaDummy530)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy529)
              (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy525))
                (Wff.classEq (Class.cv (nb078AlphaDummy529))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy530)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy526) ≠ (nb078AlphaDummy529) from (by
          unfold nb078AlphaDummy529;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy526) ≠ (nb078AlphaDummy530) from (by
            unfold nb078AlphaDummy530;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0542 (g : Var) :
    (nb078AlphaDummy528 g) ∈
      (((Class.cv (nb078AlphaDummy528 g))).fv ∪ ((Class.cv (nb078AlphaDummy527 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0543 (g : Var) :
    (nb078AlphaDummy528 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy531 g)
              (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy528 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                  (synCphi (Class.cv (nb078AlphaDummy532 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy531 g)
              (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy527 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy532 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy528 g) ≠ (nb078AlphaDummy531 g) from (by
          unfold nb078AlphaDummy531;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0542 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy528 g) ≠ (nb078AlphaDummy532 g) from (by
            unfold nb078AlphaDummy532;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0542 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0544 :
    (nb078AlphaDummy526) ∈
      (((Class.cab (nb078AlphaDummy529)
            (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy526))
              (Wff.classEq (Class.cv (nb078AlphaDummy529))
                (synCphi (Class.cv (nb078AlphaDummy530))))))).fv ∪
        ((Class.cab (nb078AlphaDummy529)
            (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy526))
              (Wff.classEq (Class.cv (nb078AlphaDummy529))
                (synCphi (Class.cv (nb078AlphaDummy530))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy526) ≠ (nb078AlphaDummy529) from (by
          unfold nb078AlphaDummy529;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy526) ≠ (nb078AlphaDummy530) from (by
            unfold nb078AlphaDummy530;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0545 (g : Var) :
    (nb078AlphaDummy528 g) ∈
      (((Class.cab (nb078AlphaDummy531 g)
            (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy528 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                (synCphi (Class.cv (nb078AlphaDummy532 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy531 g)
            (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy528 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                (synCphi (Class.cv (nb078AlphaDummy532 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy528 g) ≠ (nb078AlphaDummy531 g) from (by
          unfold nb078AlphaDummy531;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0542 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy528 g) ≠ (nb078AlphaDummy532 g) from (by
            unfold nb078AlphaDummy532;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0542 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0546 :
    (nb078AlphaDummy530) ∈ (((Class.cv (nb078AlphaDummy530))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0547 (g : Var) :
    (nb078AlphaDummy532 g) ∈ (((Class.cv (nb078AlphaDummy532 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0548 :
    (nb078AlphaDummy537) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy537)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy537)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy537))).fv) :=
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

theorem nb078_support_mem_0549 (g : Var) :
    (nb078AlphaDummy539 g) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy539 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy539 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy539 g))).fv) :=
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

theorem nb078_support_mem_0550 :
    (nb078AlphaDummy537) ∈
      (((Class.cv (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0551 (g : Var) :
    (nb078AlphaDummy539 g) ∈
      (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0552 :
    (nb078AlphaDummy544) ∈
      (((synCnin (Class.cv (nb078AlphaDummy544)) (Class.cv (nb078AlphaDummy545)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy544))
            (Class.cv (nb078AlphaDummy545)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0553 (g : Var) :
    (nb078AlphaDummy547 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy547 g))
            (Class.cv (nb078AlphaDummy548 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy547 g))
            (Class.cv (nb078AlphaDummy548 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0554 :
    (nb078AlphaDummy544) ∈
      (((Class.cv (nb078AlphaDummy544))).fv ∪ ((Class.cv (nb078AlphaDummy545))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0555 (g : Var) :
    (nb078AlphaDummy547 g) ∈
      (((Class.cv (nb078AlphaDummy547 g))).fv ∪ ((Class.cv (nb078AlphaDummy548 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0556 :
    (nb078AlphaDummy545) ∈
      (((synCnin (Class.cv (nb078AlphaDummy544)) (Class.cv (nb078AlphaDummy545)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy544))
            (Class.cv (nb078AlphaDummy545)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0557 (g : Var) :
    (nb078AlphaDummy548 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy547 g))
            (Class.cv (nb078AlphaDummy548 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy547 g))
            (Class.cv (nb078AlphaDummy548 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0558 :
    (nb078AlphaDummy545) ∈
      (((Class.cv (nb078AlphaDummy544))).fv ∪ ((Class.cv (nb078AlphaDummy545))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0559 (g : Var) :
    (nb078AlphaDummy548 g) ∈
      (((Class.cv (nb078AlphaDummy547 g))).fv ∪ ((Class.cv (nb078AlphaDummy548 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0560 :
    (nb078AlphaDummy544) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy544)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy545)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0561 (g : Var) :
    (nb078AlphaDummy547 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy547 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy548 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0562 :
    (nb078AlphaDummy544) ∈
      (((Class.cv (nb078AlphaDummy544))).fv ∪ ((Class.cv (nb078AlphaDummy544))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0563 (g : Var) :
    (nb078AlphaDummy547 g) ∈
      (((Class.cv (nb078AlphaDummy547 g))).fv ∪ ((Class.cv (nb078AlphaDummy547 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0564 :
    (nb078AlphaDummy545) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy544)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy545)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0565 (g : Var) :
    (nb078AlphaDummy548 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy547 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy548 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0566 :
    (nb078AlphaDummy545) ∈
      (((Class.cv (nb078AlphaDummy545))).fv ∪ ((Class.cv (nb078AlphaDummy545))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0567 (g : Var) :
    (nb078AlphaDummy548 g) ∈
      (((Class.cv (nb078AlphaDummy548 g))).fv ∪ ((Class.cv (nb078AlphaDummy548 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0568 :
    (nb078AlphaDummy525) ∈
      (((Class.cv (nb078AlphaDummy526))).fv ∪ ((Class.cv (nb078AlphaDummy525))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0569 :
    (nb078AlphaDummy525) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy529)
              (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy526))
                (Wff.classEq (Class.cv (nb078AlphaDummy529))
                  (synCphi (Class.cv (nb078AlphaDummy530)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy529)
              (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy525))
                (Wff.classEq (Class.cv (nb078AlphaDummy529))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy530)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy529) from (by
          unfold nb078AlphaDummy529;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0568) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy530) from (by
            unfold nb078AlphaDummy530;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0568) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0570 (g : Var) :
    (nb078AlphaDummy527 g) ∈
      (((Class.cv (nb078AlphaDummy528 g))).fv ∪ ((Class.cv (nb078AlphaDummy527 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0571 (g : Var) :
    (nb078AlphaDummy527 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy531 g)
              (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy528 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                  (synCphi (Class.cv (nb078AlphaDummy532 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy531 g)
              (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy527 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy532 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy531 g) from (by
          unfold nb078AlphaDummy531;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0570 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy532 g) from (by
            unfold nb078AlphaDummy532;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0570 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0572 :
    (nb078AlphaDummy525) ∈
      (((Class.cab (nb078AlphaDummy529)
            (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy525))
              (Wff.classEq (Class.cv (nb078AlphaDummy529))
                (synCun (synCphi (Class.cv (nb078AlphaDummy530)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy529)
            (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy525))
              (Wff.classEq (Class.cv (nb078AlphaDummy529))
                (synCun (synCphi (Class.cv (nb078AlphaDummy530)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy529) from (by
          unfold nb078AlphaDummy529;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0568) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy530) from (by
            unfold nb078AlphaDummy530;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0568) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0573 (g : Var) :
    (nb078AlphaDummy527 g) ∈
      (((Class.cab (nb078AlphaDummy531 g)
            (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy527 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy532 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy531 g)
            (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy527 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy532 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy531 g) from (by
          unfold nb078AlphaDummy531;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0570 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy532 g) from (by
            unfold nb078AlphaDummy532;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0570 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0574 :
    (nb078AlphaDummy530) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy530))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0575 (g : Var) :
    (nb078AlphaDummy532 g) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy532 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0576 :
    (nb078AlphaDummy530) ∈
      (((synCphi (Class.cv (nb078AlphaDummy530)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy530)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0577 (g : Var) :
    (nb078AlphaDummy532 g) ∈
      (((synCphi (Class.cv (nb078AlphaDummy532 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy532 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0578 :
    (nb078AlphaDummy001) ∈
      (((synCnin (synCrn (Class.cv (nb078AlphaDummy001)))
            (Class.cv (nb078AlphaDummy003)))).fv ∪
        ((synCnin (synCrn (Class.cv (nb078AlphaDummy001)))
            (Class.cv (nb078AlphaDummy003)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0579 (x : Var) (g : Var) :
    g ∈
      (((synCnin (synCrn (Class.cv g)) (Class.cv x))).fv ∪
        ((synCnin (synCrn (Class.cv g)) (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0580 :
    (nb078AlphaDummy001) ∈
      (((synCrn (Class.cv (nb078AlphaDummy001)))).fv ∪
        ((Class.cv (nb078AlphaDummy003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0581 (x : Var) (g : Var) :
    g ∈ (((synCrn (Class.cv g))).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0582 :
    (nb078AlphaDummy001) ∈
      (((Class.cv (nb078AlphaDummy001))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0583 (g : Var) : g ∈ (((Class.cv g)).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0584 :
    (nb078AlphaDummy003) ∈
      (((synCnin (synCrn (Class.cv (nb078AlphaDummy001)))
            (Class.cv (nb078AlphaDummy003)))).fv ∪
        ((synCnin (synCrn (Class.cv (nb078AlphaDummy001)))
            (Class.cv (nb078AlphaDummy003)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0585 (x : Var) (g : Var) :
    x ∈
      (((synCnin (synCrn (Class.cv g)) (Class.cv x))).fv ∪
        ((synCnin (synCrn (Class.cv g)) (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0586 :
    (nb078AlphaDummy003) ∈
      (((synCrn (Class.cv (nb078AlphaDummy001)))).fv ∪
        ((Class.cv (nb078AlphaDummy003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0587 (x : Var) (g : Var) :
    x ∈ (((synCrn (Class.cv g))).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0588 :
    (nb078AlphaDummy569) ∈
      (({(nb078AlphaDummy569)} : Finset Var) ∪ ({(nb078AlphaDummy570)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy571) (synWa (synWbr (Class.cv (nb078AlphaDummy569))
                (synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))
                (Class.cv (nb078AlphaDummy571))) (synWbr (Class.cv (nb078AlphaDummy571))
                (synCcnv (Class.cv (nb078AlphaDummy001)))
                (Class.cv (nb078AlphaDummy570)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0589 (g : Var) :
    (nb078AlphaDummy572 g) ∈
      (({(nb078AlphaDummy572 g)} : Finset Var) ∪ ({(nb078AlphaDummy573 g)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy574 g) (synWa
              (synWbr (Class.cv (nb078AlphaDummy572 g))
                (synCcnv (synCcnv (Class.cv g))) (Class.cv (nb078AlphaDummy574 g)))
              (synWbr (Class.cv (nb078AlphaDummy574 g)) (synCcnv (Class.cv g))
                (Class.cv (nb078AlphaDummy573 g)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0590 :
    (nb078AlphaDummy570) ∈
      (({(nb078AlphaDummy569)} : Finset Var) ∪ ({(nb078AlphaDummy570)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy571) (synWa (synWbr (Class.cv (nb078AlphaDummy569))
                (synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))
                (Class.cv (nb078AlphaDummy571))) (synWbr (Class.cv (nb078AlphaDummy571))
                (synCcnv (Class.cv (nb078AlphaDummy001)))
                (Class.cv (nb078AlphaDummy570)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0591 (g : Var) :
    (nb078AlphaDummy573 g) ∈
      (({(nb078AlphaDummy572 g)} : Finset Var) ∪ ({(nb078AlphaDummy573 g)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy574 g) (synWa
              (synWbr (Class.cv (nb078AlphaDummy572 g))
                (synCcnv (synCcnv (Class.cv g))) (Class.cv (nb078AlphaDummy574 g)))
              (synWbr (Class.cv (nb078AlphaDummy574 g)) (synCcnv (Class.cv g))
                (Class.cv (nb078AlphaDummy573 g)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0592 :
    (nb078AlphaDummy569) ∈
      (((Class.cv (nb078AlphaDummy569))).fv ∪ ((Class.cv (nb078AlphaDummy570))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0593 :
    (nb078AlphaDummy569) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy577)
              (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy569))
                (Wff.classEq (Class.cv (nb078AlphaDummy577))
                  (synCphi (Class.cv (nb078AlphaDummy578)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy577)
              (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy570))
                (Wff.classEq (Class.cv (nb078AlphaDummy577))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy578)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy577) from (by
          unfold nb078AlphaDummy577;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy578) from (by
            unfold nb078AlphaDummy578;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0594 (g : Var) :
    (nb078AlphaDummy572 g) ∈
      (((Class.cv (nb078AlphaDummy572 g))).fv ∪ ((Class.cv (nb078AlphaDummy573 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0595 (g : Var) :
    (nb078AlphaDummy572 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy579 g)
              (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy572 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                  (synCphi (Class.cv (nb078AlphaDummy580 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy579 g)
              (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy573 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy580 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy579 g) from (by
          unfold nb078AlphaDummy579;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0594 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy580 g) from (by
            unfold nb078AlphaDummy580;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0594 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
