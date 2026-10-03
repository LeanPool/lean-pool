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
    (nb068_alpha_dummy_350) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_350)) (Class.cv (nb068_alpha_dummy_351)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_350))
            (Class.cv (nb068_alpha_dummy_351)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0357 (f : Var) :
    (nb068_alpha_dummy_353 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_353 f))
            (Class.cv (nb068_alpha_dummy_354 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_353 f))
            (Class.cv (nb068_alpha_dummy_354 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0358 :
    (nb068_alpha_dummy_350) ∈
      (((Class.cv (nb068_alpha_dummy_350))).fv ∪ ((Class.cv (nb068_alpha_dummy_351))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0359 (f : Var) :
    (nb068_alpha_dummy_353 f) ∈
      (((Class.cv (nb068_alpha_dummy_353 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_354 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0360 :
    (nb068_alpha_dummy_351) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_350)) (Class.cv (nb068_alpha_dummy_351)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_350))
            (Class.cv (nb068_alpha_dummy_351)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0361 (f : Var) :
    (nb068_alpha_dummy_354 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_353 f))
            (Class.cv (nb068_alpha_dummy_354 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_353 f))
            (Class.cv (nb068_alpha_dummy_354 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0362 :
    (nb068_alpha_dummy_351) ∈
      (((Class.cv (nb068_alpha_dummy_350))).fv ∪ ((Class.cv (nb068_alpha_dummy_351))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0363 (f : Var) :
    (nb068_alpha_dummy_354 f) ∈
      (((Class.cv (nb068_alpha_dummy_353 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_354 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0364 :
    (nb068_alpha_dummy_350) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_350)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_351)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0365 (f : Var) :
    (nb068_alpha_dummy_353 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_353 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_354 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0366 :
    (nb068_alpha_dummy_350) ∈
      (((Class.cv (nb068_alpha_dummy_350))).fv ∪ ((Class.cv (nb068_alpha_dummy_350))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0367 (f : Var) :
    (nb068_alpha_dummy_353 f) ∈
      (((Class.cv (nb068_alpha_dummy_353 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_353 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0368 :
    (nb068_alpha_dummy_351) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_350)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_351)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0369 (f : Var) :
    (nb068_alpha_dummy_354 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_353 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_354 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0370 :
    (nb068_alpha_dummy_351) ∈
      (((Class.cv (nb068_alpha_dummy_351))).fv ∪ ((Class.cv (nb068_alpha_dummy_351))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0371 (f : Var) :
    (nb068_alpha_dummy_354 f) ∈
      (((Class.cv (nb068_alpha_dummy_354 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_354 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0372 :
    (nb068_alpha_dummy_328) ∈
      (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0373 :
    (nb068_alpha_dummy_328) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_335)
              (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_336)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_335)
              (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_335) from (by
          unfold nb068_alpha_dummy_335;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0372) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_336) from (by
            unfold nb068_alpha_dummy_336;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0372) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0374 (f : Var) :
    (nb068_alpha_dummy_331 f) ∈
      (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0375 (f : Var) :
    (nb068_alpha_dummy_331 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_337 f)
              (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_337 f)
              (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_337 f) from (by
          unfold nb068_alpha_dummy_337;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0374 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_338 f) from (by
            unfold nb068_alpha_dummy_338;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0374 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0376 :
    (nb068_alpha_dummy_328) ∈
      (((Class.cab (nb068_alpha_dummy_335)
            (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_335)
            (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_335) from (by
          unfold nb068_alpha_dummy_335;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0372) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_336) from (by
            unfold nb068_alpha_dummy_336;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0372) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0377 (f : Var) :
    (nb068_alpha_dummy_331 f) ∈
      (((Class.cab (nb068_alpha_dummy_337 f)
            (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_337 f)
            (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_337 f) from (by
          unfold nb068_alpha_dummy_337;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0374 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_338 f) from (by
            unfold nb068_alpha_dummy_338;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0374 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0378 :
    (nb068_alpha_dummy_336) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_336))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0379 (f : Var) :
    (nb068_alpha_dummy_338 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0380 :
    (nb068_alpha_dummy_336) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_336)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_336)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0381 (f : Var) :
    (nb068_alpha_dummy_338 f) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0382 :
    (nb068_alpha_dummy_327) ∈
      (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_329))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0383 :
    (nb068_alpha_dummy_327) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_371)
              (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_327))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_372)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_371)
              (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_371) from (by
          unfold nb068_alpha_dummy_371;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0382) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_372) from (by
            unfold nb068_alpha_dummy_372;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0382) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0384 (f : Var) :
    (nb068_alpha_dummy_330 f) ∈
      (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_332 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0385 (f : Var) :
    (nb068_alpha_dummy_330 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_373 f)
              (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_330 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_373 f)
              (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_330 f) ≠ (nb068_alpha_dummy_373 f) from (by
          unfold nb068_alpha_dummy_373;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0384 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_330 f) ≠ (nb068_alpha_dummy_374 f) from (by
            unfold nb068_alpha_dummy_374;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0384 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0386 :
    (nb068_alpha_dummy_327) ∈
      (((Class.cab (nb068_alpha_dummy_371)
            (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_327))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                (syn_cphi (Class.cv (nb068_alpha_dummy_372))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_371)
            (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_327))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                (syn_cphi (Class.cv (nb068_alpha_dummy_372))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_371) from (by
          unfold nb068_alpha_dummy_371;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0382) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_372) from (by
            unfold nb068_alpha_dummy_372;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0382) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0387 (f : Var) :
    (nb068_alpha_dummy_330 f) ∈
      (((Class.cab (nb068_alpha_dummy_373 f)
            (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_330 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_373 f)
            (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_330 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_330 f) ≠ (nb068_alpha_dummy_373 f) from (by
          unfold nb068_alpha_dummy_373;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0384 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_330 f) ≠ (nb068_alpha_dummy_374 f) from (by
            unfold nb068_alpha_dummy_374;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0384 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0388 :
    (nb068_alpha_dummy_372) ∈ (((Class.cv (nb068_alpha_dummy_372))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0389 (f : Var) :
    (nb068_alpha_dummy_374 f) ∈ (((Class.cv (nb068_alpha_dummy_374 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0390 :
    (nb068_alpha_dummy_379) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_379)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_379)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_379))).fv) :=
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
    (nb068_alpha_dummy_381 f) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_381 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_381 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_381 f))).fv) :=
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
    (nb068_alpha_dummy_379) ∈
      (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0393 (f : Var) :
    (nb068_alpha_dummy_381 f) ∈
      (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0394 :
    (nb068_alpha_dummy_386) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_386)) (Class.cv (nb068_alpha_dummy_387)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_386))
            (Class.cv (nb068_alpha_dummy_387)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0395 (f : Var) :
    (nb068_alpha_dummy_389 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_389 f))
            (Class.cv (nb068_alpha_dummy_390 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_389 f))
            (Class.cv (nb068_alpha_dummy_390 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0396 :
    (nb068_alpha_dummy_386) ∈
      (((Class.cv (nb068_alpha_dummy_386))).fv ∪ ((Class.cv (nb068_alpha_dummy_387))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0397 (f : Var) :
    (nb068_alpha_dummy_389 f) ∈
      (((Class.cv (nb068_alpha_dummy_389 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_390 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0398 :
    (nb068_alpha_dummy_387) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_386)) (Class.cv (nb068_alpha_dummy_387)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_386))
            (Class.cv (nb068_alpha_dummy_387)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0399 (f : Var) :
    (nb068_alpha_dummy_390 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_389 f))
            (Class.cv (nb068_alpha_dummy_390 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_389 f))
            (Class.cv (nb068_alpha_dummy_390 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0400 :
    (nb068_alpha_dummy_387) ∈
      (((Class.cv (nb068_alpha_dummy_386))).fv ∪ ((Class.cv (nb068_alpha_dummy_387))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0401 (f : Var) :
    (nb068_alpha_dummy_390 f) ∈
      (((Class.cv (nb068_alpha_dummy_389 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_390 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0402 :
    (nb068_alpha_dummy_386) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_386)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_387)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0403 (f : Var) :
    (nb068_alpha_dummy_389 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_389 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_390 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0404 :
    (nb068_alpha_dummy_386) ∈
      (((Class.cv (nb068_alpha_dummy_386))).fv ∪ ((Class.cv (nb068_alpha_dummy_386))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0405 (f : Var) :
    (nb068_alpha_dummy_389 f) ∈
      (((Class.cv (nb068_alpha_dummy_389 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_389 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0406 :
    (nb068_alpha_dummy_387) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_386)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_387)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0407 (f : Var) :
    (nb068_alpha_dummy_390 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_389 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_390 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0408 :
    (nb068_alpha_dummy_387) ∈
      (((Class.cv (nb068_alpha_dummy_387))).fv ∪ ((Class.cv (nb068_alpha_dummy_387))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0409 (f : Var) :
    (nb068_alpha_dummy_390 f) ∈
      (((Class.cv (nb068_alpha_dummy_390 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_390 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0410 :
    (nb068_alpha_dummy_329) ∈
      (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_329))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0411 :
    (nb068_alpha_dummy_329) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_371)
              (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_327))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_372)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_371)
              (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_329) ≠ (nb068_alpha_dummy_371) from (by
          unfold nb068_alpha_dummy_371;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0410) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_329) ≠ (nb068_alpha_dummy_372) from (by
            unfold nb068_alpha_dummy_372;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0410) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0412 (f : Var) :
    (nb068_alpha_dummy_332 f) ∈
      (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_332 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0413 (f : Var) :
    (nb068_alpha_dummy_332 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_373 f)
              (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_330 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_373 f)
              (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_332 f) ≠ (nb068_alpha_dummy_373 f) from (by
          unfold nb068_alpha_dummy_373;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0412 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_332 f) ≠ (nb068_alpha_dummy_374 f) from (by
            unfold nb068_alpha_dummy_374;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0412 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0414 :
    (nb068_alpha_dummy_329) ∈
      (((Class.cab (nb068_alpha_dummy_371)
            (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_371)
            (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_329) ≠ (nb068_alpha_dummy_371) from (by
          unfold nb068_alpha_dummy_371;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0410) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_329) ≠ (nb068_alpha_dummy_372) from (by
            unfold nb068_alpha_dummy_372;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0410) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0415 (f : Var) :
    (nb068_alpha_dummy_332 f) ∈
      (((Class.cab (nb068_alpha_dummy_373 f)
            (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_373 f)
            (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_332 f) ≠ (nb068_alpha_dummy_373 f) from (by
          unfold nb068_alpha_dummy_373;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0412 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_332 f) ≠ (nb068_alpha_dummy_374 f) from (by
            unfold nb068_alpha_dummy_374;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0412 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0416 :
    (nb068_alpha_dummy_372) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_372))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0417 (f : Var) :
    (nb068_alpha_dummy_374 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0418 :
    (nb068_alpha_dummy_372) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_372)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_372)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0419 (f : Var) :
    (nb068_alpha_dummy_374 f) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0420 :
    (nb068_alpha_dummy_407) ∈
      (({(nb068_alpha_dummy_407)} : Finset Var) ∪ ({(nb068_alpha_dummy_408)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb068_alpha_dummy_408))
            (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
            (Class.cv (nb068_alpha_dummy_407)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0421 (f : Var) :
    (nb068_alpha_dummy_409 f) ∈
      (({(nb068_alpha_dummy_409 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_410 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb068_alpha_dummy_410 f)) (syn_ccnv (Class.cv f))
            (Class.cv (nb068_alpha_dummy_409 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0422 :
    (nb068_alpha_dummy_408) ∈
      (({(nb068_alpha_dummy_407)} : Finset Var) ∪ ({(nb068_alpha_dummy_408)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb068_alpha_dummy_408))
            (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
            (Class.cv (nb068_alpha_dummy_407)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0423 (f : Var) :
    (nb068_alpha_dummy_410 f) ∈
      (({(nb068_alpha_dummy_409 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_410 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb068_alpha_dummy_410 f)) (syn_ccnv (Class.cv f))
            (Class.cv (nb068_alpha_dummy_409 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0424 :
    (nb068_alpha_dummy_407) ∈
      (((Class.cv (nb068_alpha_dummy_407))).fv ∪ ((Class.cv (nb068_alpha_dummy_408))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0425 :
    (nb068_alpha_dummy_407) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_413)
              (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_407))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_414)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_413)
              (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_413) from (by
          unfold nb068_alpha_dummy_413;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0424) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_414) from (by
            unfold nb068_alpha_dummy_414;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0424) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0426 (f : Var) :
    (nb068_alpha_dummy_409 f) ∈
      (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_410 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0427 (f : Var) :
    (nb068_alpha_dummy_409 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_415 f)
              (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_415 f)
              (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_409 f) ≠ (nb068_alpha_dummy_415 f) from (by
          unfold nb068_alpha_dummy_415;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0426 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_409 f) ≠ (nb068_alpha_dummy_416 f) from (by
            unfold nb068_alpha_dummy_416;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0426 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0428 :
    (nb068_alpha_dummy_407) ∈
      (((Class.cab (nb068_alpha_dummy_413)
            (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_407))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                (syn_cphi (Class.cv (nb068_alpha_dummy_414))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_413)
            (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_407))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                (syn_cphi (Class.cv (nb068_alpha_dummy_414))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_413) from (by
          unfold nb068_alpha_dummy_413;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0424) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_414) from (by
            unfold nb068_alpha_dummy_414;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0424) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0429 (f : Var) :
    (nb068_alpha_dummy_409 f) ∈
      (((Class.cab (nb068_alpha_dummy_415 f)
            (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_415 f)
            (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_409 f) ≠ (nb068_alpha_dummy_415 f) from (by
          unfold nb068_alpha_dummy_415;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0426 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_409 f) ≠ (nb068_alpha_dummy_416 f) from (by
            unfold nb068_alpha_dummy_416;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0426 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0430 :
    (nb068_alpha_dummy_414) ∈ (((Class.cv (nb068_alpha_dummy_414))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0431 (f : Var) :
    (nb068_alpha_dummy_416 f) ∈ (((Class.cv (nb068_alpha_dummy_416 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0432 :
    (nb068_alpha_dummy_421) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_421)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_421)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_421))).fv) :=
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
    (nb068_alpha_dummy_423 f) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_423 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_423 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_423 f))).fv) :=
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
    (nb068_alpha_dummy_421) ∈
      (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0435 (f : Var) :
    (nb068_alpha_dummy_423 f) ∈
      (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0436 :
    (nb068_alpha_dummy_428) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_428)) (Class.cv (nb068_alpha_dummy_429)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_428))
            (Class.cv (nb068_alpha_dummy_429)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0437 (f : Var) :
    (nb068_alpha_dummy_431 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_431 f))
            (Class.cv (nb068_alpha_dummy_432 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_431 f))
            (Class.cv (nb068_alpha_dummy_432 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0438 :
    (nb068_alpha_dummy_428) ∈
      (((Class.cv (nb068_alpha_dummy_428))).fv ∪ ((Class.cv (nb068_alpha_dummy_429))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0439 (f : Var) :
    (nb068_alpha_dummy_431 f) ∈
      (((Class.cv (nb068_alpha_dummy_431 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_432 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0440 :
    (nb068_alpha_dummy_429) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_428)) (Class.cv (nb068_alpha_dummy_429)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_428))
            (Class.cv (nb068_alpha_dummy_429)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0441 (f : Var) :
    (nb068_alpha_dummy_432 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_431 f))
            (Class.cv (nb068_alpha_dummy_432 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_431 f))
            (Class.cv (nb068_alpha_dummy_432 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0442 :
    (nb068_alpha_dummy_429) ∈
      (((Class.cv (nb068_alpha_dummy_428))).fv ∪ ((Class.cv (nb068_alpha_dummy_429))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0443 (f : Var) :
    (nb068_alpha_dummy_432 f) ∈
      (((Class.cv (nb068_alpha_dummy_431 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_432 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0444 :
    (nb068_alpha_dummy_428) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_428)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_429)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0445 (f : Var) :
    (nb068_alpha_dummy_431 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_431 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_432 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0446 :
    (nb068_alpha_dummy_428) ∈
      (((Class.cv (nb068_alpha_dummy_428))).fv ∪ ((Class.cv (nb068_alpha_dummy_428))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0447 (f : Var) :
    (nb068_alpha_dummy_431 f) ∈
      (((Class.cv (nb068_alpha_dummy_431 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_431 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0448 :
    (nb068_alpha_dummy_429) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_428)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_429)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0449 (f : Var) :
    (nb068_alpha_dummy_432 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_431 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_432 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0450 :
    (nb068_alpha_dummy_429) ∈
      (((Class.cv (nb068_alpha_dummy_429))).fv ∪ ((Class.cv (nb068_alpha_dummy_429))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0451 (f : Var) :
    (nb068_alpha_dummy_432 f) ∈
      (((Class.cv (nb068_alpha_dummy_432 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_432 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0452 :
    (nb068_alpha_dummy_408) ∈
      (((Class.cv (nb068_alpha_dummy_407))).fv ∪ ((Class.cv (nb068_alpha_dummy_408))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0453 :
    (nb068_alpha_dummy_408) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_413)
              (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_407))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_414)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_413)
              (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_413) from (by
          unfold nb068_alpha_dummy_413;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0452) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_414) from (by
            unfold nb068_alpha_dummy_414;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0452) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0454 (f : Var) :
    (nb068_alpha_dummy_410 f) ∈
      (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_410 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0455 (f : Var) :
    (nb068_alpha_dummy_410 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_415 f)
              (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_415 f)
              (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_415 f) from (by
          unfold nb068_alpha_dummy_415;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0454 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_416 f) from (by
            unfold nb068_alpha_dummy_416;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0454 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0456 :
    (nb068_alpha_dummy_408) ∈
      (((Class.cab (nb068_alpha_dummy_413)
            (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_413)
            (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_413) from (by
          unfold nb068_alpha_dummy_413;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0452) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_414) from (by
            unfold nb068_alpha_dummy_414;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0452) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0457 (f : Var) :
    (nb068_alpha_dummy_410 f) ∈
      (((Class.cab (nb068_alpha_dummy_415 f)
            (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_415 f)
            (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_415 f) from (by
          unfold nb068_alpha_dummy_415;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0454 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_416 f) from (by
            unfold nb068_alpha_dummy_416;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0454 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0458 :
    (nb068_alpha_dummy_414) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_414))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0459 (f : Var) :
    (nb068_alpha_dummy_416 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0460 :
    (nb068_alpha_dummy_414) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_414)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_414)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0461 (f : Var) :
    (nb068_alpha_dummy_416 f) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0462 :
    (nb068_alpha_dummy_408) ∈
      (((Class.cv (nb068_alpha_dummy_408))).fv ∪ ((Class.cv (nb068_alpha_dummy_407))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0463 :
    (nb068_alpha_dummy_408) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_449)
              (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_408))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_450)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_449)
              (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_407))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_450)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_449) from (by
          unfold nb068_alpha_dummy_449;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0462) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_450) from (by
            unfold nb068_alpha_dummy_450;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0462) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0464 (f : Var) :
    (nb068_alpha_dummy_410 f) ∈
      (((Class.cv (nb068_alpha_dummy_410 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_409 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0465 (f : Var) :
    (nb068_alpha_dummy_410 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_451 f)
              (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_410 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_451 f)
              (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_409 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_451 f) from (by
          unfold nb068_alpha_dummy_451;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0464 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_452 f) from (by
            unfold nb068_alpha_dummy_452;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0464 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0466 :
    (nb068_alpha_dummy_408) ∈
      (((Class.cab (nb068_alpha_dummy_449)
            (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_408))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                (syn_cphi (Class.cv (nb068_alpha_dummy_450))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_449)
            (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_408))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                (syn_cphi (Class.cv (nb068_alpha_dummy_450))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_449) from (by
          unfold nb068_alpha_dummy_449;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0462) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_450) from (by
            unfold nb068_alpha_dummy_450;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0462) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0467 (f : Var) :
    (nb068_alpha_dummy_410 f) ∈
      (((Class.cab (nb068_alpha_dummy_451 f)
            (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_410 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_451 f)
            (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_410 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_451 f) from (by
          unfold nb068_alpha_dummy_451;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0464 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_452 f) from (by
            unfold nb068_alpha_dummy_452;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0464 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0468 :
    (nb068_alpha_dummy_450) ∈ (((Class.cv (nb068_alpha_dummy_450))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0469 (f : Var) :
    (nb068_alpha_dummy_452 f) ∈ (((Class.cv (nb068_alpha_dummy_452 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0470 :
    (nb068_alpha_dummy_457) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_457)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_457)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_457))).fv) :=
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
    (nb068_alpha_dummy_459 f) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_459 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_459 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_459 f))).fv) :=
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
    (nb068_alpha_dummy_457) ∈
      (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0473 (f : Var) :
    (nb068_alpha_dummy_459 f) ∈
      (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0474 :
    (nb068_alpha_dummy_464) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_464)) (Class.cv (nb068_alpha_dummy_465)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_464))
            (Class.cv (nb068_alpha_dummy_465)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0475 (f : Var) :
    (nb068_alpha_dummy_467 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_467 f))
            (Class.cv (nb068_alpha_dummy_468 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_467 f))
            (Class.cv (nb068_alpha_dummy_468 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0476 :
    (nb068_alpha_dummy_464) ∈
      (((Class.cv (nb068_alpha_dummy_464))).fv ∪ ((Class.cv (nb068_alpha_dummy_465))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0477 (f : Var) :
    (nb068_alpha_dummy_467 f) ∈
      (((Class.cv (nb068_alpha_dummy_467 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_468 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0478 :
    (nb068_alpha_dummy_465) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_464)) (Class.cv (nb068_alpha_dummy_465)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_464))
            (Class.cv (nb068_alpha_dummy_465)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0479 (f : Var) :
    (nb068_alpha_dummy_468 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_467 f))
            (Class.cv (nb068_alpha_dummy_468 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_467 f))
            (Class.cv (nb068_alpha_dummy_468 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0480 :
    (nb068_alpha_dummy_465) ∈
      (((Class.cv (nb068_alpha_dummy_464))).fv ∪ ((Class.cv (nb068_alpha_dummy_465))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0481 (f : Var) :
    (nb068_alpha_dummy_468 f) ∈
      (((Class.cv (nb068_alpha_dummy_467 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_468 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0482 :
    (nb068_alpha_dummy_464) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_464)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_465)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0483 (f : Var) :
    (nb068_alpha_dummy_467 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_467 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_468 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0484 :
    (nb068_alpha_dummy_464) ∈
      (((Class.cv (nb068_alpha_dummy_464))).fv ∪ ((Class.cv (nb068_alpha_dummy_464))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0485 (f : Var) :
    (nb068_alpha_dummy_467 f) ∈
      (((Class.cv (nb068_alpha_dummy_467 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_467 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0486 :
    (nb068_alpha_dummy_465) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_464)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_465)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0487 (f : Var) :
    (nb068_alpha_dummy_468 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_467 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_468 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0488 :
    (nb068_alpha_dummy_465) ∈
      (((Class.cv (nb068_alpha_dummy_465))).fv ∪ ((Class.cv (nb068_alpha_dummy_465))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0489 (f : Var) :
    (nb068_alpha_dummy_468 f) ∈
      (((Class.cv (nb068_alpha_dummy_468 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_468 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0490 :
    (nb068_alpha_dummy_407) ∈
      (((Class.cv (nb068_alpha_dummy_408))).fv ∪ ((Class.cv (nb068_alpha_dummy_407))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0491 :
    (nb068_alpha_dummy_407) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_449)
              (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_408))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_450)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_449)
              (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_407))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_450)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_449) from (by
          unfold nb068_alpha_dummy_449;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0490) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_450) from (by
            unfold nb068_alpha_dummy_450;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0490) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0492 (f : Var) :
    (nb068_alpha_dummy_409 f) ∈
      (((Class.cv (nb068_alpha_dummy_410 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_409 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0493 (f : Var) :
    (nb068_alpha_dummy_409 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_451 f)
              (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_410 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_451 f)
              (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_409 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_409 f) ≠ (nb068_alpha_dummy_451 f) from (by
          unfold nb068_alpha_dummy_451;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0492 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_409 f) ≠ (nb068_alpha_dummy_452 f) from (by
            unfold nb068_alpha_dummy_452;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0492 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0494 :
    (nb068_alpha_dummy_407) ∈
      (((Class.cab (nb068_alpha_dummy_449)
            (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_407))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_450)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_449)
            (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_407))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_450)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_449) from (by
          unfold nb068_alpha_dummy_449;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0490) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_450) from (by
            unfold nb068_alpha_dummy_450;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0490) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0495 (f : Var) :
    (nb068_alpha_dummy_409 f) ∈
      (((Class.cab (nb068_alpha_dummy_451 f)
            (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_409 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_451 f)
            (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_409 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_409 f) ≠ (nb068_alpha_dummy_451 f) from (by
          unfold nb068_alpha_dummy_451;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0492 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_409 f) ≠ (nb068_alpha_dummy_452 f) from (by
            unfold nb068_alpha_dummy_452;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0492 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0496 :
    (nb068_alpha_dummy_450) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_450))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0497 (f : Var) :
    (nb068_alpha_dummy_452 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
