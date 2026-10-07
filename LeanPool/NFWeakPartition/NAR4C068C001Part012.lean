/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C068C001Block003

/-! NF weak partition development: NAR4C068C001Part012. -/


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

theorem nb068_support_mem_0356 :
    (nb068AlphaDummy350) ∈
      (((synCnin (Class.cv (nb068AlphaDummy350)) (Class.cv (nb068AlphaDummy351)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy350))
            (Class.cv (nb068AlphaDummy351)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0357 (f : Var) :
    (nb068AlphaDummy353 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy353 f))
            (Class.cv (nb068AlphaDummy354 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy353 f))
            (Class.cv (nb068AlphaDummy354 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0358 :
    (nb068AlphaDummy350) ∈
      (((Class.cv (nb068AlphaDummy350))).fv ∪ ((Class.cv (nb068AlphaDummy351))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0359 (f : Var) :
    (nb068AlphaDummy353 f) ∈
      (((Class.cv (nb068AlphaDummy353 f))).fv ∪ ((Class.cv (nb068AlphaDummy354 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0360 :
    (nb068AlphaDummy351) ∈
      (((synCnin (Class.cv (nb068AlphaDummy350)) (Class.cv (nb068AlphaDummy351)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy350))
            (Class.cv (nb068AlphaDummy351)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0361 (f : Var) :
    (nb068AlphaDummy354 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy353 f))
            (Class.cv (nb068AlphaDummy354 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy353 f))
            (Class.cv (nb068AlphaDummy354 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0362 :
    (nb068AlphaDummy351) ∈
      (((Class.cv (nb068AlphaDummy350))).fv ∪ ((Class.cv (nb068AlphaDummy351))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0363 (f : Var) :
    (nb068AlphaDummy354 f) ∈
      (((Class.cv (nb068AlphaDummy353 f))).fv ∪ ((Class.cv (nb068AlphaDummy354 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0364 :
    (nb068AlphaDummy350) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy350)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy351)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0365 (f : Var) :
    (nb068AlphaDummy353 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy353 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy354 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0366 :
    (nb068AlphaDummy350) ∈
      (((Class.cv (nb068AlphaDummy350))).fv ∪ ((Class.cv (nb068AlphaDummy350))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0367 (f : Var) :
    (nb068AlphaDummy353 f) ∈
      (((Class.cv (nb068AlphaDummy353 f))).fv ∪ ((Class.cv (nb068AlphaDummy353 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0368 :
    (nb068AlphaDummy351) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy350)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy351)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0369 (f : Var) :
    (nb068AlphaDummy354 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy353 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy354 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0370 :
    (nb068AlphaDummy351) ∈
      (((Class.cv (nb068AlphaDummy351))).fv ∪ ((Class.cv (nb068AlphaDummy351))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0371 (f : Var) :
    (nb068AlphaDummy354 f) ∈
      (((Class.cv (nb068AlphaDummy354 f))).fv ∪ ((Class.cv (nb068AlphaDummy354 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0372 :
    (nb068AlphaDummy328) ∈
      (((Class.cv (nb068AlphaDummy327))).fv ∪ ((Class.cv (nb068AlphaDummy328))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0373 :
    (nb068AlphaDummy328) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy335)
              (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy327))
                (Wff.classEq (Class.cv (nb068AlphaDummy335))
                  (synCphi (Class.cv (nb068AlphaDummy336)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy335)
              (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy328))
                (Wff.classEq (Class.cv (nb068AlphaDummy335))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy336)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy335) from (by
          unfold nb068AlphaDummy335;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0372) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy336) from (by
            unfold nb068AlphaDummy336;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0372) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0374 (f : Var) :
    (nb068AlphaDummy331 f) ∈
      (((Class.cv (nb068AlphaDummy330 f))).fv ∪ ((Class.cv (nb068AlphaDummy331 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0375 (f : Var) :
    (nb068AlphaDummy331 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy337 f)
              (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy330 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                  (synCphi (Class.cv (nb068AlphaDummy338 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy337 f)
              (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy331 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy338 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy337 f) from (by
          unfold nb068AlphaDummy337;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0374 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy338 f) from (by
            unfold nb068AlphaDummy338;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0374 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0376 :
    (nb068AlphaDummy328) ∈
      (((Class.cab (nb068AlphaDummy335)
            (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy328))
              (Wff.classEq (Class.cv (nb068AlphaDummy335))
                (synCun (synCphi (Class.cv (nb068AlphaDummy336)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy335)
            (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy328))
              (Wff.classEq (Class.cv (nb068AlphaDummy335))
                (synCun (synCphi (Class.cv (nb068AlphaDummy336)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy335) from (by
          unfold nb068AlphaDummy335;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0372) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy336) from (by
            unfold nb068AlphaDummy336;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0372) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0377 (f : Var) :
    (nb068AlphaDummy331 f) ∈
      (((Class.cab (nb068AlphaDummy337 f)
            (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy331 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy338 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy337 f)
            (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy331 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy338 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy337 f) from (by
          unfold nb068AlphaDummy337;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0374 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy338 f) from (by
            unfold nb068AlphaDummy338;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0374 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0378 :
    (nb068AlphaDummy336) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy336))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0379 (f : Var) :
    (nb068AlphaDummy338 f) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy338 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0380 :
    (nb068AlphaDummy336) ∈
      (((synCphi (Class.cv (nb068AlphaDummy336)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy336)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0381 (f : Var) :
    (nb068AlphaDummy338 f) ∈
      (((synCphi (Class.cv (nb068AlphaDummy338 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy338 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0382 :
    (nb068AlphaDummy327) ∈
      (((Class.cv (nb068AlphaDummy327))).fv ∪ ((Class.cv (nb068AlphaDummy329))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0383 :
    (nb068AlphaDummy327) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy371)
              (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy327))
                (Wff.classEq (Class.cv (nb068AlphaDummy371))
                  (synCphi (Class.cv (nb068AlphaDummy372)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy371)
              (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy329))
                (Wff.classEq (Class.cv (nb068AlphaDummy371))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy372)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy327) ≠ (nb068AlphaDummy371) from (by
          unfold nb068AlphaDummy371;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0382) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy327) ≠ (nb068AlphaDummy372) from (by
            unfold nb068AlphaDummy372;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0382) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0384 (f : Var) :
    (nb068AlphaDummy330 f) ∈
      (((Class.cv (nb068AlphaDummy330 f))).fv ∪ ((Class.cv (nb068AlphaDummy332 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0385 (f : Var) :
    (nb068AlphaDummy330 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy373 f)
              (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy330 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                  (synCphi (Class.cv (nb068AlphaDummy374 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy373 f)
              (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy332 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy374 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy330 f) ≠ (nb068AlphaDummy373 f) from (by
          unfold nb068AlphaDummy373;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0384 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy330 f) ≠ (nb068AlphaDummy374 f) from (by
            unfold nb068AlphaDummy374;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0384 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0386 :
    (nb068AlphaDummy327) ∈
      (((Class.cab (nb068AlphaDummy371)
            (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy327))
              (Wff.classEq (Class.cv (nb068AlphaDummy371))
                (synCphi (Class.cv (nb068AlphaDummy372))))))).fv ∪
        ((Class.cab (nb068AlphaDummy371)
            (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy327))
              (Wff.classEq (Class.cv (nb068AlphaDummy371))
                (synCphi (Class.cv (nb068AlphaDummy372))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy327) ≠ (nb068AlphaDummy371) from (by
          unfold nb068AlphaDummy371;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0382) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy327) ≠ (nb068AlphaDummy372) from (by
            unfold nb068AlphaDummy372;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0382) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0387 (f : Var) :
    (nb068AlphaDummy330 f) ∈
      (((Class.cab (nb068AlphaDummy373 f)
            (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy330 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                (synCphi (Class.cv (nb068AlphaDummy374 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy373 f)
            (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy330 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                (synCphi (Class.cv (nb068AlphaDummy374 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy330 f) ≠ (nb068AlphaDummy373 f) from (by
          unfold nb068AlphaDummy373;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0384 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy330 f) ≠ (nb068AlphaDummy374 f) from (by
            unfold nb068AlphaDummy374;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0384 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0388 :
    (nb068AlphaDummy372) ∈ (((Class.cv (nb068AlphaDummy372))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0389 (f : Var) :
    (nb068AlphaDummy374 f) ∈ (((Class.cv (nb068AlphaDummy374 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0390 :
    (nb068AlphaDummy379) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy379)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy379)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy379))).fv) :=
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

theorem nb068_support_mem_0391 (f : Var) :
    (nb068AlphaDummy381 f) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy381 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy381 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy381 f))).fv) :=
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

theorem nb068_support_mem_0392 :
    (nb068AlphaDummy379) ∈
      (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0393 (f : Var) :
    (nb068AlphaDummy381 f) ∈
      (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0394 :
    (nb068AlphaDummy386) ∈
      (((synCnin (Class.cv (nb068AlphaDummy386)) (Class.cv (nb068AlphaDummy387)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy386))
            (Class.cv (nb068AlphaDummy387)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0395 (f : Var) :
    (nb068AlphaDummy389 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy389 f))
            (Class.cv (nb068AlphaDummy390 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy389 f))
            (Class.cv (nb068AlphaDummy390 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0396 :
    (nb068AlphaDummy386) ∈
      (((Class.cv (nb068AlphaDummy386))).fv ∪ ((Class.cv (nb068AlphaDummy387))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0397 (f : Var) :
    (nb068AlphaDummy389 f) ∈
      (((Class.cv (nb068AlphaDummy389 f))).fv ∪ ((Class.cv (nb068AlphaDummy390 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0398 :
    (nb068AlphaDummy387) ∈
      (((synCnin (Class.cv (nb068AlphaDummy386)) (Class.cv (nb068AlphaDummy387)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy386))
            (Class.cv (nb068AlphaDummy387)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0399 (f : Var) :
    (nb068AlphaDummy390 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy389 f))
            (Class.cv (nb068AlphaDummy390 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy389 f))
            (Class.cv (nb068AlphaDummy390 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0400 :
    (nb068AlphaDummy387) ∈
      (((Class.cv (nb068AlphaDummy386))).fv ∪ ((Class.cv (nb068AlphaDummy387))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0401 (f : Var) :
    (nb068AlphaDummy390 f) ∈
      (((Class.cv (nb068AlphaDummy389 f))).fv ∪ ((Class.cv (nb068AlphaDummy390 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0402 :
    (nb068AlphaDummy386) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy386)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy387)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0403 (f : Var) :
    (nb068AlphaDummy389 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy389 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy390 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0404 :
    (nb068AlphaDummy386) ∈
      (((Class.cv (nb068AlphaDummy386))).fv ∪ ((Class.cv (nb068AlphaDummy386))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0405 (f : Var) :
    (nb068AlphaDummy389 f) ∈
      (((Class.cv (nb068AlphaDummy389 f))).fv ∪ ((Class.cv (nb068AlphaDummy389 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0406 :
    (nb068AlphaDummy387) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy386)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy387)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0407 (f : Var) :
    (nb068AlphaDummy390 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy389 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy390 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0408 :
    (nb068AlphaDummy387) ∈
      (((Class.cv (nb068AlphaDummy387))).fv ∪ ((Class.cv (nb068AlphaDummy387))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0409 (f : Var) :
    (nb068AlphaDummy390 f) ∈
      (((Class.cv (nb068AlphaDummy390 f))).fv ∪ ((Class.cv (nb068AlphaDummy390 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0410 :
    (nb068AlphaDummy329) ∈
      (((Class.cv (nb068AlphaDummy327))).fv ∪ ((Class.cv (nb068AlphaDummy329))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0411 :
    (nb068AlphaDummy329) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy371)
              (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy327))
                (Wff.classEq (Class.cv (nb068AlphaDummy371))
                  (synCphi (Class.cv (nb068AlphaDummy372)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy371)
              (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy329))
                (Wff.classEq (Class.cv (nb068AlphaDummy371))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy372)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy329) ≠ (nb068AlphaDummy371) from (by
          unfold nb068AlphaDummy371;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0410) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy329) ≠ (nb068AlphaDummy372) from (by
            unfold nb068AlphaDummy372;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0410) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0412 (f : Var) :
    (nb068AlphaDummy332 f) ∈
      (((Class.cv (nb068AlphaDummy330 f))).fv ∪ ((Class.cv (nb068AlphaDummy332 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0413 (f : Var) :
    (nb068AlphaDummy332 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy373 f)
              (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy330 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                  (synCphi (Class.cv (nb068AlphaDummy374 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy373 f)
              (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy332 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy374 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy332 f) ≠ (nb068AlphaDummy373 f) from (by
          unfold nb068AlphaDummy373;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0412 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy332 f) ≠ (nb068AlphaDummy374 f) from (by
            unfold nb068AlphaDummy374;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0412 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0414 :
    (nb068AlphaDummy329) ∈
      (((Class.cab (nb068AlphaDummy371)
            (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy329))
              (Wff.classEq (Class.cv (nb068AlphaDummy371))
                (synCun (synCphi (Class.cv (nb068AlphaDummy372)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy371)
            (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy329))
              (Wff.classEq (Class.cv (nb068AlphaDummy371))
                (synCun (synCphi (Class.cv (nb068AlphaDummy372)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy329) ≠ (nb068AlphaDummy371) from (by
          unfold nb068AlphaDummy371;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0410) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy329) ≠ (nb068AlphaDummy372) from (by
            unfold nb068AlphaDummy372;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0410) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0415 (f : Var) :
    (nb068AlphaDummy332 f) ∈
      (((Class.cab (nb068AlphaDummy373 f)
            (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy332 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy374 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy373 f)
            (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy332 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy374 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy332 f) ≠ (nb068AlphaDummy373 f) from (by
          unfold nb068AlphaDummy373;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0412 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy332 f) ≠ (nb068AlphaDummy374 f) from (by
            unfold nb068AlphaDummy374;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0412 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0416 :
    (nb068AlphaDummy372) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy372))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0417 (f : Var) :
    (nb068AlphaDummy374 f) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy374 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0418 :
    (nb068AlphaDummy372) ∈
      (((synCphi (Class.cv (nb068AlphaDummy372)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy372)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0419 (f : Var) :
    (nb068AlphaDummy374 f) ∈
      (((synCphi (Class.cv (nb068AlphaDummy374 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy374 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0420 :
    (nb068AlphaDummy407) ∈
      (({(nb068AlphaDummy407)} : Finset Var) ∪ ({(nb068AlphaDummy408)} : Finset Var) ∪
        ((synWbr (Class.cv (nb068AlphaDummy408))
            (synCcnv (Class.cv (nb068AlphaDummy000)))
            (Class.cv (nb068AlphaDummy407)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0421 (f : Var) :
    (nb068AlphaDummy409 f) ∈
      (({(nb068AlphaDummy409 f)} : Finset Var) ∪ ({(nb068AlphaDummy410 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb068AlphaDummy410 f)) (synCcnv (Class.cv f))
            (Class.cv (nb068AlphaDummy409 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0422 :
    (nb068AlphaDummy408) ∈
      (({(nb068AlphaDummy407)} : Finset Var) ∪ ({(nb068AlphaDummy408)} : Finset Var) ∪
        ((synWbr (Class.cv (nb068AlphaDummy408))
            (synCcnv (Class.cv (nb068AlphaDummy000)))
            (Class.cv (nb068AlphaDummy407)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0423 (f : Var) :
    (nb068AlphaDummy410 f) ∈
      (({(nb068AlphaDummy409 f)} : Finset Var) ∪ ({(nb068AlphaDummy410 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb068AlphaDummy410 f)) (synCcnv (Class.cv f))
            (Class.cv (nb068AlphaDummy409 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0424 :
    (nb068AlphaDummy407) ∈
      (((Class.cv (nb068AlphaDummy407))).fv ∪ ((Class.cv (nb068AlphaDummy408))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0425 :
    (nb068AlphaDummy407) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy413)
              (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy407))
                (Wff.classEq (Class.cv (nb068AlphaDummy413))
                  (synCphi (Class.cv (nb068AlphaDummy414)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy413)
              (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy408))
                (Wff.classEq (Class.cv (nb068AlphaDummy413))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy414)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy407) ≠ (nb068AlphaDummy413) from (by
          unfold nb068AlphaDummy413;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0424) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy407) ≠ (nb068AlphaDummy414) from (by
            unfold nb068AlphaDummy414;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0424) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0426 (f : Var) :
    (nb068AlphaDummy409 f) ∈
      (((Class.cv (nb068AlphaDummy409 f))).fv ∪ ((Class.cv (nb068AlphaDummy410 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0427 (f : Var) :
    (nb068AlphaDummy409 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy415 f)
              (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy409 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                  (synCphi (Class.cv (nb068AlphaDummy416 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy415 f)
              (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy410 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy416 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy409 f) ≠ (nb068AlphaDummy415 f) from (by
          unfold nb068AlphaDummy415;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0426 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy409 f) ≠ (nb068AlphaDummy416 f) from (by
            unfold nb068AlphaDummy416;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0426 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0428 :
    (nb068AlphaDummy407) ∈
      (((Class.cab (nb068AlphaDummy413)
            (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy407))
              (Wff.classEq (Class.cv (nb068AlphaDummy413))
                (synCphi (Class.cv (nb068AlphaDummy414))))))).fv ∪
        ((Class.cab (nb068AlphaDummy413)
            (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy407))
              (Wff.classEq (Class.cv (nb068AlphaDummy413))
                (synCphi (Class.cv (nb068AlphaDummy414))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy407) ≠ (nb068AlphaDummy413) from (by
          unfold nb068AlphaDummy413;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0424) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy407) ≠ (nb068AlphaDummy414) from (by
            unfold nb068AlphaDummy414;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0424) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0429 (f : Var) :
    (nb068AlphaDummy409 f) ∈
      (((Class.cab (nb068AlphaDummy415 f)
            (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy409 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                (synCphi (Class.cv (nb068AlphaDummy416 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy415 f)
            (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy409 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                (synCphi (Class.cv (nb068AlphaDummy416 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy409 f) ≠ (nb068AlphaDummy415 f) from (by
          unfold nb068AlphaDummy415;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0426 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy409 f) ≠ (nb068AlphaDummy416 f) from (by
            unfold nb068AlphaDummy416;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0426 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0430 :
    (nb068AlphaDummy414) ∈ (((Class.cv (nb068AlphaDummy414))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0431 (f : Var) :
    (nb068AlphaDummy416 f) ∈ (((Class.cv (nb068AlphaDummy416 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0432 :
    (nb068AlphaDummy421) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy421)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy421)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy421))).fv) :=
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

theorem nb068_support_mem_0433 (f : Var) :
    (nb068AlphaDummy423 f) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy423 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy423 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy423 f))).fv) :=
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

theorem nb068_support_mem_0434 :
    (nb068AlphaDummy421) ∈
      (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0435 (f : Var) :
    (nb068AlphaDummy423 f) ∈
      (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0436 :
    (nb068AlphaDummy428) ∈
      (((synCnin (Class.cv (nb068AlphaDummy428)) (Class.cv (nb068AlphaDummy429)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy428))
            (Class.cv (nb068AlphaDummy429)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0437 (f : Var) :
    (nb068AlphaDummy431 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy431 f))
            (Class.cv (nb068AlphaDummy432 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy431 f))
            (Class.cv (nb068AlphaDummy432 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0438 :
    (nb068AlphaDummy428) ∈
      (((Class.cv (nb068AlphaDummy428))).fv ∪ ((Class.cv (nb068AlphaDummy429))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0439 (f : Var) :
    (nb068AlphaDummy431 f) ∈
      (((Class.cv (nb068AlphaDummy431 f))).fv ∪ ((Class.cv (nb068AlphaDummy432 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0440 :
    (nb068AlphaDummy429) ∈
      (((synCnin (Class.cv (nb068AlphaDummy428)) (Class.cv (nb068AlphaDummy429)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy428))
            (Class.cv (nb068AlphaDummy429)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0441 (f : Var) :
    (nb068AlphaDummy432 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy431 f))
            (Class.cv (nb068AlphaDummy432 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy431 f))
            (Class.cv (nb068AlphaDummy432 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0442 :
    (nb068AlphaDummy429) ∈
      (((Class.cv (nb068AlphaDummy428))).fv ∪ ((Class.cv (nb068AlphaDummy429))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0443 (f : Var) :
    (nb068AlphaDummy432 f) ∈
      (((Class.cv (nb068AlphaDummy431 f))).fv ∪ ((Class.cv (nb068AlphaDummy432 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0444 :
    (nb068AlphaDummy428) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy428)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy429)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0445 (f : Var) :
    (nb068AlphaDummy431 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy431 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy432 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0446 :
    (nb068AlphaDummy428) ∈
      (((Class.cv (nb068AlphaDummy428))).fv ∪ ((Class.cv (nb068AlphaDummy428))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0447 (f : Var) :
    (nb068AlphaDummy431 f) ∈
      (((Class.cv (nb068AlphaDummy431 f))).fv ∪ ((Class.cv (nb068AlphaDummy431 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0448 :
    (nb068AlphaDummy429) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy428)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy429)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0449 (f : Var) :
    (nb068AlphaDummy432 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy431 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy432 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0450 :
    (nb068AlphaDummy429) ∈
      (((Class.cv (nb068AlphaDummy429))).fv ∪ ((Class.cv (nb068AlphaDummy429))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0451 (f : Var) :
    (nb068AlphaDummy432 f) ∈
      (((Class.cv (nb068AlphaDummy432 f))).fv ∪ ((Class.cv (nb068AlphaDummy432 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0452 :
    (nb068AlphaDummy408) ∈
      (((Class.cv (nb068AlphaDummy407))).fv ∪ ((Class.cv (nb068AlphaDummy408))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0453 :
    (nb068AlphaDummy408) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy413)
              (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy407))
                (Wff.classEq (Class.cv (nb068AlphaDummy413))
                  (synCphi (Class.cv (nb068AlphaDummy414)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy413)
              (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy408))
                (Wff.classEq (Class.cv (nb068AlphaDummy413))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy414)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy408) ≠ (nb068AlphaDummy413) from (by
          unfold nb068AlphaDummy413;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0452) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy408) ≠ (nb068AlphaDummy414) from (by
            unfold nb068AlphaDummy414;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0452) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0454 (f : Var) :
    (nb068AlphaDummy410 f) ∈
      (((Class.cv (nb068AlphaDummy409 f))).fv ∪ ((Class.cv (nb068AlphaDummy410 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0455 (f : Var) :
    (nb068AlphaDummy410 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy415 f)
              (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy409 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                  (synCphi (Class.cv (nb068AlphaDummy416 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy415 f)
              (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy410 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy416 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy410 f) ≠ (nb068AlphaDummy415 f) from (by
          unfold nb068AlphaDummy415;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0454 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy410 f) ≠ (nb068AlphaDummy416 f) from (by
            unfold nb068AlphaDummy416;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0454 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0456 :
    (nb068AlphaDummy408) ∈
      (((Class.cab (nb068AlphaDummy413)
            (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy408))
              (Wff.classEq (Class.cv (nb068AlphaDummy413))
                (synCun (synCphi (Class.cv (nb068AlphaDummy414)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy413)
            (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy408))
              (Wff.classEq (Class.cv (nb068AlphaDummy413))
                (synCun (synCphi (Class.cv (nb068AlphaDummy414)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy408) ≠ (nb068AlphaDummy413) from (by
          unfold nb068AlphaDummy413;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0452) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy408) ≠ (nb068AlphaDummy414) from (by
            unfold nb068AlphaDummy414;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0452) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0457 (f : Var) :
    (nb068AlphaDummy410 f) ∈
      (((Class.cab (nb068AlphaDummy415 f)
            (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy410 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy416 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy415 f)
            (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy410 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy416 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy410 f) ≠ (nb068AlphaDummy415 f) from (by
          unfold nb068AlphaDummy415;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0454 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy410 f) ≠ (nb068AlphaDummy416 f) from (by
            unfold nb068AlphaDummy416;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0454 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0458 :
    (nb068AlphaDummy414) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy414))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0459 (f : Var) :
    (nb068AlphaDummy416 f) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy416 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0460 :
    (nb068AlphaDummy414) ∈
      (((synCphi (Class.cv (nb068AlphaDummy414)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy414)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0461 (f : Var) :
    (nb068AlphaDummy416 f) ∈
      (((synCphi (Class.cv (nb068AlphaDummy416 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy416 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0462 :
    (nb068AlphaDummy408) ∈
      (((Class.cv (nb068AlphaDummy408))).fv ∪ ((Class.cv (nb068AlphaDummy407))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0463 :
    (nb068AlphaDummy408) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy449)
              (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy408))
                (Wff.classEq (Class.cv (nb068AlphaDummy449))
                  (synCphi (Class.cv (nb068AlphaDummy450)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy449)
              (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy407))
                (Wff.classEq (Class.cv (nb068AlphaDummy449))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy450)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy408) ≠ (nb068AlphaDummy449) from (by
          unfold nb068AlphaDummy449;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0462) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy408) ≠ (nb068AlphaDummy450) from (by
            unfold nb068AlphaDummy450;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0462) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0464 (f : Var) :
    (nb068AlphaDummy410 f) ∈
      (((Class.cv (nb068AlphaDummy410 f))).fv ∪ ((Class.cv (nb068AlphaDummy409 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0465 (f : Var) :
    (nb068AlphaDummy410 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy451 f)
              (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy410 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                  (synCphi (Class.cv (nb068AlphaDummy452 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy451 f)
              (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy409 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy452 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy410 f) ≠ (nb068AlphaDummy451 f) from (by
          unfold nb068AlphaDummy451;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0464 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy410 f) ≠ (nb068AlphaDummy452 f) from (by
            unfold nb068AlphaDummy452;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0464 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0466 :
    (nb068AlphaDummy408) ∈
      (((Class.cab (nb068AlphaDummy449)
            (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy408))
              (Wff.classEq (Class.cv (nb068AlphaDummy449))
                (synCphi (Class.cv (nb068AlphaDummy450))))))).fv ∪
        ((Class.cab (nb068AlphaDummy449)
            (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy408))
              (Wff.classEq (Class.cv (nb068AlphaDummy449))
                (synCphi (Class.cv (nb068AlphaDummy450))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy408) ≠ (nb068AlphaDummy449) from (by
          unfold nb068AlphaDummy449;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0462) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy408) ≠ (nb068AlphaDummy450) from (by
            unfold nb068AlphaDummy450;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0462) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0467 (f : Var) :
    (nb068AlphaDummy410 f) ∈
      (((Class.cab (nb068AlphaDummy451 f)
            (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy410 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                (synCphi (Class.cv (nb068AlphaDummy452 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy451 f)
            (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy410 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                (synCphi (Class.cv (nb068AlphaDummy452 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy410 f) ≠ (nb068AlphaDummy451 f) from (by
          unfold nb068AlphaDummy451;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0464 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy410 f) ≠ (nb068AlphaDummy452 f) from (by
            unfold nb068AlphaDummy452;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0464 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0468 :
    (nb068AlphaDummy450) ∈ (((Class.cv (nb068AlphaDummy450))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0469 (f : Var) :
    (nb068AlphaDummy452 f) ∈ (((Class.cv (nb068AlphaDummy452 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0470 :
    (nb068AlphaDummy457) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy457)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy457)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy457))).fv) :=
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

theorem nb068_support_mem_0471 (f : Var) :
    (nb068AlphaDummy459 f) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy459 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy459 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy459 f))).fv) :=
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

theorem nb068_support_mem_0472 :
    (nb068AlphaDummy457) ∈
      (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0473 (f : Var) :
    (nb068AlphaDummy459 f) ∈
      (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0474 :
    (nb068AlphaDummy464) ∈
      (((synCnin (Class.cv (nb068AlphaDummy464)) (Class.cv (nb068AlphaDummy465)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy464))
            (Class.cv (nb068AlphaDummy465)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0475 (f : Var) :
    (nb068AlphaDummy467 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy467 f))
            (Class.cv (nb068AlphaDummy468 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy467 f))
            (Class.cv (nb068AlphaDummy468 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0476 :
    (nb068AlphaDummy464) ∈
      (((Class.cv (nb068AlphaDummy464))).fv ∪ ((Class.cv (nb068AlphaDummy465))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0477 (f : Var) :
    (nb068AlphaDummy467 f) ∈
      (((Class.cv (nb068AlphaDummy467 f))).fv ∪ ((Class.cv (nb068AlphaDummy468 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0478 :
    (nb068AlphaDummy465) ∈
      (((synCnin (Class.cv (nb068AlphaDummy464)) (Class.cv (nb068AlphaDummy465)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy464))
            (Class.cv (nb068AlphaDummy465)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0479 (f : Var) :
    (nb068AlphaDummy468 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy467 f))
            (Class.cv (nb068AlphaDummy468 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy467 f))
            (Class.cv (nb068AlphaDummy468 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0480 :
    (nb068AlphaDummy465) ∈
      (((Class.cv (nb068AlphaDummy464))).fv ∪ ((Class.cv (nb068AlphaDummy465))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0481 (f : Var) :
    (nb068AlphaDummy468 f) ∈
      (((Class.cv (nb068AlphaDummy467 f))).fv ∪ ((Class.cv (nb068AlphaDummy468 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0482 :
    (nb068AlphaDummy464) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy464)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy465)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0483 (f : Var) :
    (nb068AlphaDummy467 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy467 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy468 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0484 :
    (nb068AlphaDummy464) ∈
      (((Class.cv (nb068AlphaDummy464))).fv ∪ ((Class.cv (nb068AlphaDummy464))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0485 (f : Var) :
    (nb068AlphaDummy467 f) ∈
      (((Class.cv (nb068AlphaDummy467 f))).fv ∪ ((Class.cv (nb068AlphaDummy467 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0486 :
    (nb068AlphaDummy465) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy464)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy465)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0487 (f : Var) :
    (nb068AlphaDummy468 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy467 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy468 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0488 :
    (nb068AlphaDummy465) ∈
      (((Class.cv (nb068AlphaDummy465))).fv ∪ ((Class.cv (nb068AlphaDummy465))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0489 (f : Var) :
    (nb068AlphaDummy468 f) ∈
      (((Class.cv (nb068AlphaDummy468 f))).fv ∪ ((Class.cv (nb068AlphaDummy468 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0490 :
    (nb068AlphaDummy407) ∈
      (((Class.cv (nb068AlphaDummy408))).fv ∪ ((Class.cv (nb068AlphaDummy407))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0491 :
    (nb068AlphaDummy407) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy449)
              (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy408))
                (Wff.classEq (Class.cv (nb068AlphaDummy449))
                  (synCphi (Class.cv (nb068AlphaDummy450)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy449)
              (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy407))
                (Wff.classEq (Class.cv (nb068AlphaDummy449))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy450)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy407) ≠ (nb068AlphaDummy449) from (by
          unfold nb068AlphaDummy449;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0490) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy407) ≠ (nb068AlphaDummy450) from (by
            unfold nb068AlphaDummy450;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0490) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0492 (f : Var) :
    (nb068AlphaDummy409 f) ∈
      (((Class.cv (nb068AlphaDummy410 f))).fv ∪ ((Class.cv (nb068AlphaDummy409 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0493 (f : Var) :
    (nb068AlphaDummy409 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy451 f)
              (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy410 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                  (synCphi (Class.cv (nb068AlphaDummy452 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy451 f)
              (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy409 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy452 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy409 f) ≠ (nb068AlphaDummy451 f) from (by
          unfold nb068AlphaDummy451;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0492 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy409 f) ≠ (nb068AlphaDummy452 f) from (by
            unfold nb068AlphaDummy452;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0492 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0494 :
    (nb068AlphaDummy407) ∈
      (((Class.cab (nb068AlphaDummy449)
            (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy407))
              (Wff.classEq (Class.cv (nb068AlphaDummy449))
                (synCun (synCphi (Class.cv (nb068AlphaDummy450)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy449)
            (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy407))
              (Wff.classEq (Class.cv (nb068AlphaDummy449))
                (synCun (synCphi (Class.cv (nb068AlphaDummy450)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy407) ≠ (nb068AlphaDummy449) from (by
          unfold nb068AlphaDummy449;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0490) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy407) ≠ (nb068AlphaDummy450) from (by
            unfold nb068AlphaDummy450;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0490) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0495 (f : Var) :
    (nb068AlphaDummy409 f) ∈
      (((Class.cab (nb068AlphaDummy451 f)
            (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy409 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy452 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy451 f)
            (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy409 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy452 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy409 f) ≠ (nb068AlphaDummy451 f) from (by
          unfold nb068AlphaDummy451;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0492 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy409 f) ≠ (nb068AlphaDummy452 f) from (by
            unfold nb068AlphaDummy452;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0492 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0496 :
    (nb068AlphaDummy450) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy450))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0497 (f : Var) :
    (nb068AlphaDummy452 f) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy452 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
