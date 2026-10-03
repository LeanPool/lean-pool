/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block018

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part056`. -/


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

@[expose]
noncomputable def nb090_split_alpha_0033 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_h_v : h ≠ v) :
    TAlphaWff
      [((nb090_alpha_dummy_387 A), (nb090_alpha_dummy_388 v)),
        ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)),
        ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
        ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
        ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)),
        ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
        ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
        ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_387 A))
          (Class.cab (nb090_alpha_dummy_381 A)
            (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_387 A))
            (Class.cab (nb090_alpha_dummy_381 A)
              (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_388 v))
          (Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_388 v))
            (Class.cab (nb090_alpha_dummy_383 v)
              (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_382 A) from (by
                      unfold nb090_alpha_dummy_382;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0392 A) 1))))
                  (show v ≠ (nb090_alpha_dummy_384 v) from (by
                      unfold nb090_alpha_dummy_384;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0394 v) 1))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_381 A) from (by
                        unfold nb090_alpha_dummy_381;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0392 A) 0))))
                    (show v ≠ (nb090_alpha_dummy_383 v) from (by
                        unfold nb090_alpha_dummy_383;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0394 v) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_387 A) from (by
                          unfold nb090_alpha_dummy_387;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0396 A) 0))))
                      (show v ≠ (nb090_alpha_dummy_388 v) from (by
                          unfold nb090_alpha_dummy_388;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0397 v) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_385 A) from (by
                            unfold nb090_alpha_dummy_385;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0393 A) 0))))
                        (show v ≠ (nb090_alpha_dummy_386 v) from (by
                            unfold nb090_alpha_dummy_386;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0395 v) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_373 A) from (by
                              unfold nb090_alpha_dummy_373;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0386 A) 0))))
                          (show v ≠ (nb090_alpha_dummy_374 v) from (by
                              unfold nb090_alpha_dummy_374;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0389 v) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_375 A) from (by
                                unfold nb090_alpha_dummy_375;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0387 A) 0))))
                            (show v ≠ (nb090_alpha_dummy_376 v) from (by
                                unfold nb090_alpha_dummy_376;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0390 v) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_378 A) from
                                (by
                                  unfold nb090_alpha_dummy_378;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0388 A) 1))))
                              (show v ≠ (nb090_alpha_dummy_380 v) from (by
                                  unfold nb090_alpha_dummy_380;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0391 v) 1))))
                              (TAlphaVar.there (show
                                  (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_377 A) from (by
                                    unfold nb090_alpha_dummy_377;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0388 A)
                                            0)))) (show v ≠ (nb090_alpha_dummy_379 v) from (by
                                    unfold nb090_alpha_dummy_379;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0391 v)
                                            0)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_331 A) from
                                    (by
                                      unfold nb090_alpha_dummy_331;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0384 A)
                                              0)))) (show v ≠ (nb090_alpha_dummy_332 v h) from
                                    (by
                                      unfold nb090_alpha_dummy_332;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0385 v h)
                                              0)))) (TAlphaVar.there (show
                                      (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_329 A) from
                                      (by
                                        unfold nb090_alpha_dummy_329;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0382 A)
                                                0)))) (show v ≠ (nb090_alpha_dummy_330 v h) from
                                      (by
                                        unfold nb090_alpha_dummy_330;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0383 v h) 0))))
                                    (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                      (Ne.symm dv_h_v) (TAlphaVar.here _ _ _))))))))))))))
            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_373 A))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_382 A) ≠ (nb090_alpha_dummy_389 A) from (by
                              unfold nb090_alpha_dummy_389;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0398 A) 0))))
                          (show (nb090_alpha_dummy_384 v) ≠ (nb090_alpha_dummy_391 v) from (by
                              unfold nb090_alpha_dummy_391;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0399 v) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_382 A) ≠ (nb090_alpha_dummy_390 A) from (by
                                unfold nb090_alpha_dummy_390;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0398 A) 1))))
                            (show (nb090_alpha_dummy_384 v) ≠ (nb090_alpha_dummy_392 v) from (by
                                unfold nb090_alpha_dummy_392;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0399 v) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_382 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_384 v))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_396 A) from (by
          unfold nb090_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0402 A) 1)))) (show (nb090_alpha_dummy_391 v) ≠
        (nb090_alpha_dummy_399 v) from (by
          unfold nb090_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0403 v) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_395 A) from (by
          unfold nb090_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0402 A) 0)))) (show (nb090_alpha_dummy_391 v) ≠
        (nb090_alpha_dummy_398 v) from (by
          unfold nb090_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0403 v) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_393 A) from (by
          unfold nb090_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0400 A)
                  0)))) (show (nb090_alpha_dummy_391 v) ≠ (nb090_alpha_dummy_394 v) from (by
          unfold nb090_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0401 v)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_397 A), (nb090_alpha_dummy_400 v)), ((nb090_alpha_dummy_396 A),
        (nb090_alpha_dummy_399 v)), ((nb090_alpha_dummy_395 A), (nb090_alpha_dummy_398 v)),
        ((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)), ((nb090_alpha_dummy_389 A),
        (nb090_alpha_dummy_391 v)), ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)),
        ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)), ((nb090_alpha_dummy_381 A),
        (nb090_alpha_dummy_383 v)), ((nb090_alpha_dummy_387 A), (nb090_alpha_dummy_388 v)),
        ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)), ((nb090_alpha_dummy_373 A),
        (nb090_alpha_dummy_374 v)), ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
        ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)), ((nb090_alpha_dummy_377 A),
        (nb090_alpha_dummy_379 v)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
        ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_396
        A) ≠ (nb090_alpha_dummy_403 A) from (by
          unfold
            nb090_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0406
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_404 v) from (by
          unfold
            nb090_alpha_dummy_404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0407
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠
        (nb090_alpha_dummy_401 A) from (by
          unfold
            nb090_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0404
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_402 v) from (by
          unfold
            nb090_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0405
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_389
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠ (nb090_alpha_dummy_403 A) from (by
          unfold
            nb090_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0410
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_404 v) from (by
          unfold
            nb090_alpha_dummy_404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0411
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠
        (nb090_alpha_dummy_401 A) from (by
          unfold
            nb090_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0408
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_402 v) from (by
          unfold
            nb090_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0409
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠ (nb090_alpha_dummy_403 A) from (by
          unfold
            nb090_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0406
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_404 v) from (by
          unfold
            nb090_alpha_dummy_404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0407
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠
        (nb090_alpha_dummy_401 A) from (by
          unfold
            nb090_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0404
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_402 v) from (by
          unfold
            nb090_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0405
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_389
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠ (nb090_alpha_dummy_403 A) from (by
          unfold
            nb090_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0410
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_404 v) from (by
          unfold
            nb090_alpha_dummy_404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0411
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠
        (nb090_alpha_dummy_401 A) from (by
          unfold
            nb090_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0408
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_402 v) from (by
          unfold
            nb090_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0409
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_397 A), (nb090_alpha_dummy_400 v)), ((nb090_alpha_dummy_396 A),
        (nb090_alpha_dummy_399 v)), ((nb090_alpha_dummy_395 A), (nb090_alpha_dummy_398 v)),
        ((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)), ((nb090_alpha_dummy_389 A),
        (nb090_alpha_dummy_391 v)), ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)),
        ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)), ((nb090_alpha_dummy_381 A),
        (nb090_alpha_dummy_383 v)), ((nb090_alpha_dummy_387 A), (nb090_alpha_dummy_388 v)),
        ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)), ((nb090_alpha_dummy_373 A),
        (nb090_alpha_dummy_374 v)), ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
        ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)), ((nb090_alpha_dummy_377 A),
        (nb090_alpha_dummy_379 v)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
        ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_391
        v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠ (nb090_alpha_dummy_407 A) from (by
          unfold
            nb090_alpha_dummy_407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0414
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_408 v) from (by
          unfold
            nb090_alpha_dummy_408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0415
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠
        (nb090_alpha_dummy_405 A) from (by
          unfold
            nb090_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0412
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_406 v) from (by
          unfold
            nb090_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0413
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_389
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠ (nb090_alpha_dummy_407 A) from (by
          unfold
            nb090_alpha_dummy_407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0414
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_408 v) from (by
          unfold
            nb090_alpha_dummy_408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0415
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠
        (nb090_alpha_dummy_405 A) from (by
          unfold
            nb090_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0412
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_406 v) from (by
          unfold
            nb090_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0413
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_389
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_397
        A) ≠ (nb090_alpha_dummy_409 A) from (by
          unfold
            nb090_alpha_dummy_409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0418
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_410 v) from (by
          unfold
            nb090_alpha_dummy_410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0419
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠
        (nb090_alpha_dummy_405 A) from (by
          unfold
            nb090_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0416
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_406 v) from (by
          unfold
            nb090_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0417
                    v)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_397
        A) ≠ (nb090_alpha_dummy_409 A) from (by
          unfold
            nb090_alpha_dummy_409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0418
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_410 v) from (by
          unfold
            nb090_alpha_dummy_410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0419
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠
        (nb090_alpha_dummy_405 A) from (by
          unfold
            nb090_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0416
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_406 v) from (by
          unfold
            nb090_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0417
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_393 A) from
                                      (by
                                        unfold nb090_alpha_dummy_393;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0400 A)
                                                0)))) (show (nb090_alpha_dummy_391 v) ≠
                                        (nb090_alpha_dummy_394 v) from (by
                                        unfold nb090_alpha_dummy_394;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0401 v)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)),
                                    ((nb090_alpha_dummy_389 A), (nb090_alpha_dummy_391 v)),
                                    ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)),
                                    ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)),
                                    ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)),
                                    ((nb090_alpha_dummy_387 A), (nb090_alpha_dummy_388 v)),
                                    ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)),
                                    ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
                                    ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
                                    ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)),
                                    ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
                                    ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
                                    ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_393 A) from
                                    (by
                                      unfold nb090_alpha_dummy_393;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0400 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_391 v) ≠ (nb090_alpha_dummy_394 v) from
                                    (by
                                      unfold nb090_alpha_dummy_394;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0401 v)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_393 A) from
                                      (by
                                        unfold nb090_alpha_dummy_393;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0400 A)
                                                0)))) (show (nb090_alpha_dummy_391 v) ≠
                                        (nb090_alpha_dummy_394 v) from (by
                                        unfold nb090_alpha_dummy_394;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0401 v)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)),
                                    ((nb090_alpha_dummy_389 A), (nb090_alpha_dummy_391 v)),
                                    ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)),
                                    ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)),
                                    ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)),
                                    ((nb090_alpha_dummy_387 A), (nb090_alpha_dummy_388 v)),
                                    ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)),
                                    ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
                                    ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
                                    ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)),
                                    ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
                                    ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
                                    ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_382 A) from (by
                        unfold nb090_alpha_dummy_382;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0392 A) 1))))
                    (show v ≠ (nb090_alpha_dummy_384 v) from (by
                        unfold nb090_alpha_dummy_384;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0394 v) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_381 A) from (by
                          unfold nb090_alpha_dummy_381;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0392 A) 0))))
                      (show v ≠ (nb090_alpha_dummy_383 v) from (by
                          unfold nb090_alpha_dummy_383;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0394 v) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_387 A) from (by
                            unfold nb090_alpha_dummy_387;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0396 A) 0))))
                        (show v ≠ (nb090_alpha_dummy_388 v) from (by
                            unfold nb090_alpha_dummy_388;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0397 v) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_385 A) from (by
                              unfold nb090_alpha_dummy_385;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0393 A) 0))))
                          (show v ≠ (nb090_alpha_dummy_386 v) from (by
                              unfold nb090_alpha_dummy_386;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0395 v) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_373 A) from (by
                                unfold nb090_alpha_dummy_373;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0386 A) 0))))
                            (show v ≠ (nb090_alpha_dummy_374 v) from (by
                                unfold nb090_alpha_dummy_374;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0389 v) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_375 A) from
                                (by
                                  unfold nb090_alpha_dummy_375;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0387 A) 0))))
                              (show v ≠ (nb090_alpha_dummy_376 v) from (by
                                  unfold nb090_alpha_dummy_376;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0390 v) 0))))
                              (TAlphaVar.there (show
                                  (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_378 A) from (by
                                    unfold nb090_alpha_dummy_378;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0388 A)
                                            1)))) (show v ≠ (nb090_alpha_dummy_380 v) from (by
                                    unfold nb090_alpha_dummy_380;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0391 v)
                                            1)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_377 A) from
                                    (by
                                      unfold nb090_alpha_dummy_377;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0388 A)
                                              0)))) (show v ≠ (nb090_alpha_dummy_379 v) from (by
                                      unfold nb090_alpha_dummy_379;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0391 v)
                                              0)))) (TAlphaVar.there (show
                                      (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_331 A) from
                                      (by
                                        unfold nb090_alpha_dummy_331;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0384 A)
                                                0)))) (show v ≠ (nb090_alpha_dummy_332 v h) from
                                      (by
                                        unfold nb090_alpha_dummy_332;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0385 v h) 0))))
                                    (TAlphaVar.there (show (nb090_alpha_dummy_002 A) ≠
        (nb090_alpha_dummy_329 A) from (by
                                          unfold nb090_alpha_dummy_329;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0382 A) 0))))
                                      (show v ≠ (nb090_alpha_dummy_330 v h) from (by
                                          unfold nb090_alpha_dummy_330;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0383 v h) 0))))
                                      (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                        (Ne.symm dv_h_v) (TAlphaVar.here _ _ _))))))))))))))
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_373 A))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_382 A) ≠ (nb090_alpha_dummy_389 A) from (by
                                unfold nb090_alpha_dummy_389;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0398 A) 0))))
                            (show (nb090_alpha_dummy_384 v) ≠ (nb090_alpha_dummy_391 v) from (by
                                unfold nb090_alpha_dummy_391;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0399 v) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_382 A) ≠ (nb090_alpha_dummy_390 A) from
                                (by
                                  unfold nb090_alpha_dummy_390;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0398 A) 1))))
                              (show (nb090_alpha_dummy_384 v) ≠ (nb090_alpha_dummy_392 v) from
                                (by
                                  unfold nb090_alpha_dummy_392;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0399 v) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_382 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_384 v))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_396 A) from (by
          unfold nb090_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0402 A) 1)))) (show (nb090_alpha_dummy_391 v) ≠
        (nb090_alpha_dummy_399 v) from (by
          unfold nb090_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0403 v) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_395 A) from (by
          unfold nb090_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0402 A)
                  0)))) (show (nb090_alpha_dummy_391 v) ≠ (nb090_alpha_dummy_398 v) from (by
          unfold nb090_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0403 v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_389 A) ≠
        (nb090_alpha_dummy_393 A) from (by
          unfold nb090_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0400 A)
                  0)))) (show (nb090_alpha_dummy_391 v) ≠ (nb090_alpha_dummy_394 v) from (by
          unfold nb090_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0401 v)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_397 A), (nb090_alpha_dummy_400 v)), ((nb090_alpha_dummy_396 A),
        (nb090_alpha_dummy_399 v)), ((nb090_alpha_dummy_395 A), (nb090_alpha_dummy_398 v)),
        ((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)), ((nb090_alpha_dummy_389 A),
        (nb090_alpha_dummy_391 v)), ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)),
        ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)), ((nb090_alpha_dummy_381 A),
        (nb090_alpha_dummy_383 v)), ((nb090_alpha_dummy_387 A), (nb090_alpha_dummy_388 v)),
        ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)), ((nb090_alpha_dummy_373 A),
        (nb090_alpha_dummy_374 v)), ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
        ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)), ((nb090_alpha_dummy_377 A),
        (nb090_alpha_dummy_379 v)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
        ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_396
        A) ≠ (nb090_alpha_dummy_403 A) from (by
          unfold
            nb090_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0406
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_404 v) from (by
          unfold
            nb090_alpha_dummy_404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0407
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠
        (nb090_alpha_dummy_401 A) from (by
          unfold
            nb090_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0404
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_402 v) from (by
          unfold
            nb090_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0405
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_389
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠ (nb090_alpha_dummy_403 A) from (by
          unfold
            nb090_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0410
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_404 v) from (by
          unfold
            nb090_alpha_dummy_404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0411
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠
        (nb090_alpha_dummy_401 A) from (by
          unfold
            nb090_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0408
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_402 v) from (by
          unfold
            nb090_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0409
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠ (nb090_alpha_dummy_403 A) from (by
          unfold
            nb090_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0406
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_404 v) from (by
          unfold
            nb090_alpha_dummy_404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0407
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠
        (nb090_alpha_dummy_401 A) from (by
          unfold
            nb090_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0404
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_402 v) from (by
          unfold
            nb090_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0405
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_389
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠ (nb090_alpha_dummy_403 A) from (by
          unfold
            nb090_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0410
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_404 v) from (by
          unfold
            nb090_alpha_dummy_404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0411
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠
        (nb090_alpha_dummy_401 A) from (by
          unfold
            nb090_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0408
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_402 v) from (by
          unfold
            nb090_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0409
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_397 A), (nb090_alpha_dummy_400 v)), ((nb090_alpha_dummy_396 A),
        (nb090_alpha_dummy_399 v)), ((nb090_alpha_dummy_395 A), (nb090_alpha_dummy_398 v)),
        ((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)), ((nb090_alpha_dummy_389 A),
        (nb090_alpha_dummy_391 v)), ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)),
        ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)), ((nb090_alpha_dummy_381 A),
        (nb090_alpha_dummy_383 v)), ((nb090_alpha_dummy_387 A), (nb090_alpha_dummy_388 v)),
        ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)), ((nb090_alpha_dummy_373 A),
        (nb090_alpha_dummy_374 v)), ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
        ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)), ((nb090_alpha_dummy_377 A),
        (nb090_alpha_dummy_379 v)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
        ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_391
        v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠ (nb090_alpha_dummy_407 A) from (by
          unfold
            nb090_alpha_dummy_407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0414
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_408 v) from (by
          unfold
            nb090_alpha_dummy_408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0415
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠
        (nb090_alpha_dummy_405 A) from (by
          unfold
            nb090_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0412
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_406 v) from (by
          unfold
            nb090_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0413
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_389
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠ (nb090_alpha_dummy_407 A) from (by
          unfold
            nb090_alpha_dummy_407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0414
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_408 v) from (by
          unfold
            nb090_alpha_dummy_408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0415
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠
        (nb090_alpha_dummy_405 A) from (by
          unfold
            nb090_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0412
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_406 v) from (by
          unfold
            nb090_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0413
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_389
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_397
        A) ≠ (nb090_alpha_dummy_409 A) from (by
          unfold
            nb090_alpha_dummy_409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0418
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_410 v) from (by
          unfold
            nb090_alpha_dummy_410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0419
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠
        (nb090_alpha_dummy_405 A) from (by
          unfold
            nb090_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0416
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_406 v) from (by
          unfold
            nb090_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0417
                    v)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_397
        A) ≠ (nb090_alpha_dummy_409 A) from (by
          unfold
            nb090_alpha_dummy_409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0418
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_410 v) from (by
          unfold
            nb090_alpha_dummy_410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0419
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠
        (nb090_alpha_dummy_405 A) from (by
          unfold
            nb090_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0416
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_406 v) from (by
          unfold
            nb090_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0417
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_393 A)
                                        from (by
                                          unfold nb090_alpha_dummy_393;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0400 A) 0)))) (show
                                        (nb090_alpha_dummy_391 v) ≠ (nb090_alpha_dummy_394 v)
                                        from (by
                                          unfold nb090_alpha_dummy_394;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0401 v) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)),
                                      ((nb090_alpha_dummy_389 A), (nb090_alpha_dummy_391 v)),
                                      ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)),
                                      ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)),
                                      ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)),
                                      ((nb090_alpha_dummy_387 A), (nb090_alpha_dummy_388 v)),
                                      ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)),
                                      ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
                                      ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
                                      ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)),
                                      ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
                                      ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
                                      ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_393 A) from
                                      (by
                                        unfold nb090_alpha_dummy_393;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0400 A)
                                                0)))) (show (nb090_alpha_dummy_391 v) ≠
                                        (nb090_alpha_dummy_394 v) from (by
                                        unfold nb090_alpha_dummy_394;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0401 v)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_393 A)
                                        from (by
                                          unfold nb090_alpha_dummy_393;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0400 A) 0)))) (show
                                        (nb090_alpha_dummy_391 v) ≠ (nb090_alpha_dummy_394 v)
                                        from (by
                                          unfold nb090_alpha_dummy_394;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0401 v) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)),
                                      ((nb090_alpha_dummy_389 A), (nb090_alpha_dummy_391 v)),
                                      ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)),
                                      ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)),
                                      ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)),
                                      ((nb090_alpha_dummy_387 A), (nb090_alpha_dummy_388 v)),
                                      ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)),
                                      ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
                                      ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
                                      ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)),
                                      ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
                                      ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
                                      ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part057`. -/


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

@[expose]
noncomputable def nb090_split_alpha_0034 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_415 A), (nb090_alpha_dummy_416 v)),
        ((nb090_alpha_dummy_413 A), (nb090_alpha_dummy_414 v)),
        ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)),
        ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)),
        ((nb090_alpha_dummy_411 A), (nb090_alpha_dummy_412 v)),
        ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)),
        ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
        ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
        ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)),
        ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
        ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
        ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_415 A))
          (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_415 A))
            (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_416 v))
          (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_416 v))
            (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_382 A) ≠ (nb090_alpha_dummy_389 A) from (by
                      unfold nb090_alpha_dummy_389;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0398 A) 0))))
                  (show (nb090_alpha_dummy_384 v) ≠ (nb090_alpha_dummy_391 v) from (by
                      unfold nb090_alpha_dummy_391;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0399 v) 0))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_382 A) ≠ (nb090_alpha_dummy_390 A) from (by
                        unfold nb090_alpha_dummy_390;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0398 A) 1))))
                    (show (nb090_alpha_dummy_384 v) ≠ (nb090_alpha_dummy_392 v) from (by
                        unfold nb090_alpha_dummy_392;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0399 v) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_382 A) ≠ (nb090_alpha_dummy_415 A) from (by
                          unfold nb090_alpha_dummy_415;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0428 A) 0))))
                      (show (nb090_alpha_dummy_384 v) ≠ (nb090_alpha_dummy_416 v) from (by
                          unfold nb090_alpha_dummy_416;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0429 v) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_382 A) ≠ (nb090_alpha_dummy_413 A) from (by
                            unfold nb090_alpha_dummy_413;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0426 A) 0))))
                        (show (nb090_alpha_dummy_384 v) ≠ (nb090_alpha_dummy_414 v) from (by
                            unfold nb090_alpha_dummy_414;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0427 v) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_382 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_384 v))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_396 A) from
                                      (by
                                        unfold nb090_alpha_dummy_396;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0402 A)
                                                1)))) (show (nb090_alpha_dummy_391 v) ≠
                                        (nb090_alpha_dummy_399 v) from (by
                                        unfold nb090_alpha_dummy_399;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0403 v)
                                                1)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_395 A)
                                        from (by
                                          unfold nb090_alpha_dummy_395;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0402 A) 0)))) (show
                                        (nb090_alpha_dummy_391 v) ≠ (nb090_alpha_dummy_398 v)
                                        from (by
                                          unfold nb090_alpha_dummy_398;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0403 v) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_389 A) ≠
        (nb090_alpha_dummy_393 A) from (by
          unfold nb090_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0400 A) 0)))) (show (nb090_alpha_dummy_391 v) ≠
        (nb090_alpha_dummy_394 v) from (by
          unfold nb090_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0401 v) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_397 A),
        (nb090_alpha_dummy_400 v)), ((nb090_alpha_dummy_396 A), (nb090_alpha_dummy_399 v)),
                                        ((nb090_alpha_dummy_395 A), (nb090_alpha_dummy_398 v)),
                                        ((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)),
                                        ((nb090_alpha_dummy_389 A), (nb090_alpha_dummy_391 v)),
                                        ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)),
                                        ((nb090_alpha_dummy_415 A), (nb090_alpha_dummy_416 v)),
                                        ((nb090_alpha_dummy_413 A), (nb090_alpha_dummy_414 v)),
                                        ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)),
                                        ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)),
                                        ((nb090_alpha_dummy_411 A), (nb090_alpha_dummy_412 v)),
                                        ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)),
                                        ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
                                        ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
                                        ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)),
                                        ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
                                        ((nb090_alpha_dummy_331 A),
        (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                                        ((nb090_alpha_dummy_000 A), h),
                                        ((nb090_alpha_dummy_002 A), v),
                                        ((nb090_alpha_dummy_001 A), u),
                                        ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠ (nb090_alpha_dummy_403 A) from (by
          unfold
            nb090_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0406
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_404 v) from (by
          unfold
            nb090_alpha_dummy_404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0407
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠
        (nb090_alpha_dummy_401 A) from (by
          unfold
            nb090_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0404
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_402 v) from (by
          unfold
            nb090_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0405
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_389
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠
        (nb090_alpha_dummy_403 A) from (by
          unfold
            nb090_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0410
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_404 v) from (by
          unfold
            nb090_alpha_dummy_404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0411
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠
        (nb090_alpha_dummy_401 A) from (by
          unfold
            nb090_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0408
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_402 v) from (by
          unfold
            nb090_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0409
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠ (nb090_alpha_dummy_403 A) from (by
          unfold
            nb090_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0406
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_404 v) from (by
          unfold
            nb090_alpha_dummy_404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0407
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠
        (nb090_alpha_dummy_401 A) from (by
          unfold
            nb090_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0404
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_402 v) from (by
          unfold
            nb090_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0405
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_389
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠
        (nb090_alpha_dummy_403 A) from (by
          unfold
            nb090_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0410
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_404 v) from (by
          unfold
            nb090_alpha_dummy_404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0411
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠
        (nb090_alpha_dummy_401 A) from (by
          unfold
            nb090_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0408
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_402 v) from (by
          unfold
            nb090_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0409
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb090_alpha_dummy_397 A), (nb090_alpha_dummy_400 v)),
        ((nb090_alpha_dummy_396 A), (nb090_alpha_dummy_399 v)), ((nb090_alpha_dummy_395 A),
        (nb090_alpha_dummy_398 v)), ((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)),
        ((nb090_alpha_dummy_389 A), (nb090_alpha_dummy_391 v)), ((nb090_alpha_dummy_390 A),
        (nb090_alpha_dummy_392 v)), ((nb090_alpha_dummy_415 A), (nb090_alpha_dummy_416 v)),
        ((nb090_alpha_dummy_413 A), (nb090_alpha_dummy_414 v)), ((nb090_alpha_dummy_382 A),
        (nb090_alpha_dummy_384 v)), ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)),
        ((nb090_alpha_dummy_411 A), (nb090_alpha_dummy_412 v)), ((nb090_alpha_dummy_385 A),
        (nb090_alpha_dummy_386 v)), ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
        ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)), ((nb090_alpha_dummy_378 A),
        (nb090_alpha_dummy_380 v)), ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
        ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A),
        (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_396 A) ≠ (nb090_alpha_dummy_407 A) from (by
          unfold
            nb090_alpha_dummy_407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0414
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_408 v) from (by
          unfold
            nb090_alpha_dummy_408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0415
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠
        (nb090_alpha_dummy_405 A) from (by
          unfold
            nb090_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0412
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_406 v) from (by
          unfold
            nb090_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0413
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_389
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠
        (nb090_alpha_dummy_407 A) from (by
          unfold
            nb090_alpha_dummy_407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0414
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_408 v) from (by
          unfold
            nb090_alpha_dummy_408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0415
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠
        (nb090_alpha_dummy_405 A) from (by
          unfold
            nb090_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0412
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_406 v) from (by
          unfold
            nb090_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0413
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_389
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_397 A) ≠ (nb090_alpha_dummy_409 A) from (by
          unfold
            nb090_alpha_dummy_409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0418
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_410 v) from (by
          unfold
            nb090_alpha_dummy_410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0419
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠
        (nb090_alpha_dummy_405 A) from (by
          unfold
            nb090_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0416
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_406 v) from (by
          unfold
            nb090_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0417
                    v)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_397 A) ≠ (nb090_alpha_dummy_409 A) from (by
          unfold
            nb090_alpha_dummy_409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0418
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_410 v) from (by
          unfold
            nb090_alpha_dummy_410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0419
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠
        (nb090_alpha_dummy_405 A) from (by
          unfold
            nb090_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0416
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_406 v) from (by
          unfold
            nb090_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0417
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_393 A) from (by
                                unfold nb090_alpha_dummy_393;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0400 A) 0))))
                            (show (nb090_alpha_dummy_391 v) ≠ (nb090_alpha_dummy_394 v) from (by
                                unfold nb090_alpha_dummy_394;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0401 v) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)),
                            ((nb090_alpha_dummy_389 A), (nb090_alpha_dummy_391 v)),
                            ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)),
                            ((nb090_alpha_dummy_415 A), (nb090_alpha_dummy_416 v)),
                            ((nb090_alpha_dummy_413 A), (nb090_alpha_dummy_414 v)),
                            ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)),
                            ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)),
                            ((nb090_alpha_dummy_411 A), (nb090_alpha_dummy_412 v)),
                            ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)),
                            ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
                            ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
                            ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)),
                            ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
                            ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
                            ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_393 A) from (by
                              unfold nb090_alpha_dummy_393;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0400 A) 0))))
                          (show (nb090_alpha_dummy_391 v) ≠ (nb090_alpha_dummy_394 v) from (by
                              unfold nb090_alpha_dummy_394;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0401 v) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_393 A) from (by
                                unfold nb090_alpha_dummy_393;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0400 A) 0))))
                            (show (nb090_alpha_dummy_391 v) ≠ (nb090_alpha_dummy_394 v) from (by
                                unfold nb090_alpha_dummy_394;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0401 v) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)),
                            ((nb090_alpha_dummy_389 A), (nb090_alpha_dummy_391 v)),
                            ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)),
                            ((nb090_alpha_dummy_415 A), (nb090_alpha_dummy_416 v)),
                            ((nb090_alpha_dummy_413 A), (nb090_alpha_dummy_414 v)),
                            ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)),
                            ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)),
                            ((nb090_alpha_dummy_411 A), (nb090_alpha_dummy_412 v)),
                            ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)),
                            ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
                            ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
                            ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)),
                            ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
                            ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
                            ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090_alpha_dummy_382 A) ≠ (nb090_alpha_dummy_389 A) from (by
                        unfold nb090_alpha_dummy_389;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0398 A) 0))))
                    (show (nb090_alpha_dummy_384 v) ≠ (nb090_alpha_dummy_391 v) from (by
                        unfold nb090_alpha_dummy_391;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0399 v) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_382 A) ≠ (nb090_alpha_dummy_390 A) from (by
                          unfold nb090_alpha_dummy_390;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0398 A) 1))))
                      (show (nb090_alpha_dummy_384 v) ≠ (nb090_alpha_dummy_392 v) from (by
                          unfold nb090_alpha_dummy_392;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0399 v) 1))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_382 A) ≠ (nb090_alpha_dummy_415 A) from (by
                            unfold nb090_alpha_dummy_415;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0428 A) 0))))
                        (show (nb090_alpha_dummy_384 v) ≠ (nb090_alpha_dummy_416 v) from (by
                            unfold nb090_alpha_dummy_416;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0429 v) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_382 A) ≠ (nb090_alpha_dummy_413 A) from (by
                              unfold nb090_alpha_dummy_413;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0426 A) 0))))
                          (show (nb090_alpha_dummy_384 v) ≠ (nb090_alpha_dummy_414 v) from (by
                              unfold nb090_alpha_dummy_414;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0427 v) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_382 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_384 v))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090_alpha_dummy_389 A) ≠
        (nb090_alpha_dummy_396 A) from (by
                                          unfold nb090_alpha_dummy_396;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0402 A) 1)))) (show
                                        (nb090_alpha_dummy_391 v) ≠ (nb090_alpha_dummy_399 v)
                                        from (by
                                          unfold nb090_alpha_dummy_399;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0403 v) 1))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_389 A) ≠
        (nb090_alpha_dummy_395 A) from (by
          unfold nb090_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0402 A) 0)))) (show (nb090_alpha_dummy_391 v) ≠
        (nb090_alpha_dummy_398 v) from (by
          unfold nb090_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0403 v) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_393 A) from (by
          unfold nb090_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0400 A) 0)))) (show (nb090_alpha_dummy_391 v) ≠
        (nb090_alpha_dummy_394 v) from (by
          unfold nb090_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0401 v) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_397 A),
        (nb090_alpha_dummy_400 v)), ((nb090_alpha_dummy_396 A), (nb090_alpha_dummy_399 v)),
        ((nb090_alpha_dummy_395 A), (nb090_alpha_dummy_398 v)), ((nb090_alpha_dummy_393 A),
        (nb090_alpha_dummy_394 v)), ((nb090_alpha_dummy_389 A), (nb090_alpha_dummy_391 v)),
        ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)), ((nb090_alpha_dummy_415 A),
        (nb090_alpha_dummy_416 v)), ((nb090_alpha_dummy_413 A), (nb090_alpha_dummy_414 v)),
        ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)), ((nb090_alpha_dummy_381 A),
        (nb090_alpha_dummy_383 v)), ((nb090_alpha_dummy_411 A), (nb090_alpha_dummy_412 v)),
        ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)), ((nb090_alpha_dummy_373 A),
        (nb090_alpha_dummy_374 v)), ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
        ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)), ((nb090_alpha_dummy_377 A),
        (nb090_alpha_dummy_379 v)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
        ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠ (nb090_alpha_dummy_403 A) from (by
          unfold
            nb090_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0406
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_404 v) from (by
          unfold
            nb090_alpha_dummy_404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0407
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠
        (nb090_alpha_dummy_401 A) from (by
          unfold
            nb090_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0404
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_402 v) from (by
          unfold
            nb090_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0405
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_389
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠ (nb090_alpha_dummy_403 A) from (by
          unfold
            nb090_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0410
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_404 v) from (by
          unfold
            nb090_alpha_dummy_404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0411
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠
        (nb090_alpha_dummy_401 A) from (by
          unfold
            nb090_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0408
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_402 v) from (by
          unfold
            nb090_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0409
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠ (nb090_alpha_dummy_403 A) from (by
          unfold
            nb090_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0406
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_404 v) from (by
          unfold
            nb090_alpha_dummy_404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0407
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠
        (nb090_alpha_dummy_401 A) from (by
          unfold
            nb090_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0404
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_402 v) from (by
          unfold
            nb090_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0405
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_389
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠ (nb090_alpha_dummy_403 A) from (by
          unfold
            nb090_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0410
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_404 v) from (by
          unfold
            nb090_alpha_dummy_404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0411
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠
        (nb090_alpha_dummy_401 A) from (by
          unfold
            nb090_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0408
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_402 v) from (by
          unfold
            nb090_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0409
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_397 A), (nb090_alpha_dummy_400 v)), ((nb090_alpha_dummy_396 A),
        (nb090_alpha_dummy_399 v)), ((nb090_alpha_dummy_395 A), (nb090_alpha_dummy_398 v)),
        ((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)), ((nb090_alpha_dummy_389 A),
        (nb090_alpha_dummy_391 v)), ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)),
        ((nb090_alpha_dummy_415 A), (nb090_alpha_dummy_416 v)), ((nb090_alpha_dummy_413 A),
        (nb090_alpha_dummy_414 v)), ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)),
        ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)), ((nb090_alpha_dummy_411 A),
        (nb090_alpha_dummy_412 v)), ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)),
        ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)), ((nb090_alpha_dummy_375 A),
        (nb090_alpha_dummy_376 v)), ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)),
        ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)), ((nb090_alpha_dummy_331 A),
        (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_396 A) ≠ (nb090_alpha_dummy_407 A) from (by
          unfold
            nb090_alpha_dummy_407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0414
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_408 v) from (by
          unfold
            nb090_alpha_dummy_408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0415
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠
        (nb090_alpha_dummy_405 A) from (by
          unfold
            nb090_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0412
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_406 v) from (by
          unfold
            nb090_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0413
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_389
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠ (nb090_alpha_dummy_407 A) from (by
          unfold
            nb090_alpha_dummy_407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0414
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_408 v) from (by
          unfold
            nb090_alpha_dummy_408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0415
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_396 A) ≠
        (nb090_alpha_dummy_405 A) from (by
          unfold
            nb090_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0412
                    A)
                  0)))) (show (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_406 v) from (by
          unfold
            nb090_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0413
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_389
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_397 A) ≠ (nb090_alpha_dummy_409 A) from (by
          unfold
            nb090_alpha_dummy_409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0418
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_410 v) from (by
          unfold
            nb090_alpha_dummy_410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0419
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠
        (nb090_alpha_dummy_405 A) from (by
          unfold
            nb090_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0416
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_406 v) from (by
          unfold
            nb090_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0417
                    v)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_397 A) ≠ (nb090_alpha_dummy_409 A) from (by
          unfold
            nb090_alpha_dummy_409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0418
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_410 v) from (by
          unfold
            nb090_alpha_dummy_410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0419
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_397 A) ≠
        (nb090_alpha_dummy_405 A) from (by
          unfold
            nb090_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0416
                    A)
                  0)))) (show (nb090_alpha_dummy_400 v) ≠ (nb090_alpha_dummy_406 v) from (by
          unfold
            nb090_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0417
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_393 A) from
                                (by
                                  unfold nb090_alpha_dummy_393;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0400 A) 0))))
                              (show (nb090_alpha_dummy_391 v) ≠ (nb090_alpha_dummy_394 v) from
                                (by
                                  unfold nb090_alpha_dummy_394;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0401 v) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)),
                              ((nb090_alpha_dummy_389 A), (nb090_alpha_dummy_391 v)),
                              ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)),
                              ((nb090_alpha_dummy_415 A), (nb090_alpha_dummy_416 v)),
                              ((nb090_alpha_dummy_413 A), (nb090_alpha_dummy_414 v)),
                              ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)),
                              ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)),
                              ((nb090_alpha_dummy_411 A), (nb090_alpha_dummy_412 v)),
                              ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)),
                              ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
                              ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
                              ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)),
                              ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
                              ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
                              ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_393 A) from (by
                                unfold nb090_alpha_dummy_393;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0400 A) 0))))
                            (show (nb090_alpha_dummy_391 v) ≠ (nb090_alpha_dummy_394 v) from (by
                                unfold nb090_alpha_dummy_394;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0401 v) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_393 A) from
                                (by
                                  unfold nb090_alpha_dummy_393;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0400 A) 0))))
                              (show (nb090_alpha_dummy_391 v) ≠ (nb090_alpha_dummy_394 v) from
                                (by
                                  unfold nb090_alpha_dummy_394;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0401 v) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)),
                              ((nb090_alpha_dummy_389 A), (nb090_alpha_dummy_391 v)),
                              ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)),
                              ((nb090_alpha_dummy_415 A), (nb090_alpha_dummy_416 v)),
                              ((nb090_alpha_dummy_413 A), (nb090_alpha_dummy_414 v)),
                              ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)),
                              ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)),
                              ((nb090_alpha_dummy_411 A), (nb090_alpha_dummy_412 v)),
                              ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)),
                              ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
                              ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
                              ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)),
                              ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
                              ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
                              ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb090_wpp_notmem_1090 (A : Class) : (nb090_alpha_dummy_373 A) ∉ ((syn_c2nd)).fv :=
  by simpa only [nb090_alpha_dummy_373, fv_syn_c2nd] using (nb090_compact_fv_empty_0300 A)

theorem nb090_wpp_notmem_1091 (v : Var) : (nb090_alpha_dummy_374 v) ∉ ((syn_c2nd)).fv :=
  by simpa only [nb090_alpha_dummy_374, fv_syn_c2nd] using (nb090_compact_fv_empty_0301 v)

theorem nb090_wpp_notmem_1092 (A : Class) : (nb090_alpha_dummy_375 A) ∉ ((syn_c2nd)).fv :=
  by simpa only [nb090_alpha_dummy_375, fv_syn_c2nd] using (nb090_compact_fv_empty_0302 A)

theorem nb090_wpp_notmem_1093 (v : Var) : (nb090_alpha_dummy_376 v) ∉ ((syn_c2nd)).fv :=
  by simpa only [nb090_alpha_dummy_376, fv_syn_c2nd] using (nb090_compact_fv_empty_0303 v)

theorem nb090_wpp_notmem_1094 (A : Class) : (nb090_alpha_dummy_378 A) ∉ ((syn_c2nd)).fv :=
  by simpa only [nb090_alpha_dummy_378, fv_syn_c2nd] using (nb090_compact_fv_empty_0304 A)

theorem nb090_wpp_notmem_1095 (v : Var) : (nb090_alpha_dummy_380 v) ∉ ((syn_c2nd)).fv :=
  by simpa only [nb090_alpha_dummy_380, fv_syn_c2nd] using (nb090_compact_fv_empty_0305 v)

theorem nb090_wpp_notmem_1096 (A : Class) : (nb090_alpha_dummy_377 A) ∉ ((syn_c2nd)).fv :=
  by simpa only [nb090_alpha_dummy_377, fv_syn_c2nd] using (nb090_compact_fv_empty_0306 A)

theorem nb090_wpp_notmem_1097 (v : Var) : (nb090_alpha_dummy_379 v) ∉ ((syn_c2nd)).fv :=
  by simpa only [nb090_alpha_dummy_379, fv_syn_c2nd] using (nb090_compact_fv_empty_0307 v)

theorem nb090_wpp_notmem_1098 (A : Class) : (nb090_alpha_dummy_331 A) ∉ ((syn_c2nd)).fv :=
  by simpa only [nb090_alpha_dummy_331, fv_syn_c2nd] using (nb090_compact_fv_empty_0250 A)

theorem nb090_wpp_notmem_1099 (v : Var) (h : Var) :
    (nb090_alpha_dummy_332 v h) ∉ ((syn_c2nd)).fv := by
  simpa only [nb090_alpha_dummy_332, fv_syn_c2nd] using (nb090_compact_fv_empty_0251 v h)

theorem nb090_wpp_notmem_1100 (A : Class) : (nb090_alpha_dummy_329 A) ∉ ((syn_c2nd)).fv :=
  by simpa only [nb090_alpha_dummy_329, fv_syn_c2nd] using (nb090_compact_fv_empty_0252 A)

theorem nb090_wpp_notmem_1101 (v : Var) (h : Var) :
    (nb090_alpha_dummy_330 v h) ∉ ((syn_c2nd)).fv := by
  simpa only [nb090_alpha_dummy_330, fv_syn_c2nd] using (nb090_compact_fv_empty_0253 v h)

theorem nb090_compact_envfresh_0124 (v : Var) (u : Var) (A : Class) (h : Var) :
    TEnvFresh
      [((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
        ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
        ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)),
        ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
        ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
        ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      ((syn_c2nd)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb090_alpha_dummy_373 A) (nb090_alpha_dummy_374 v)
      (nb090_wpp_notmem_1090 A) (nb090_wpp_notmem_1091 v)
      (TEnvFresh.consFresh (nb090_alpha_dummy_375 A) (nb090_alpha_dummy_376 v)
        (nb090_wpp_notmem_1092 A) (nb090_wpp_notmem_1093 v)
        (TEnvFresh.consFresh (nb090_alpha_dummy_378 A) (nb090_alpha_dummy_380 v)
          (nb090_wpp_notmem_1094 A) (nb090_wpp_notmem_1095 v)
          (TEnvFresh.consFresh (nb090_alpha_dummy_377 A) (nb090_alpha_dummy_379 v)
            (nb090_wpp_notmem_1096 A) (nb090_wpp_notmem_1097 v)
            (TEnvFresh.consFresh (nb090_alpha_dummy_331 A) (nb090_alpha_dummy_332 v h)
              (nb090_wpp_notmem_1098 A) (nb090_wpp_notmem_1099 v h)
              (TEnvFresh.consFresh (nb090_alpha_dummy_329 A) (nb090_alpha_dummy_330 v h)
                (nb090_wpp_notmem_1100 A) (nb090_wpp_notmem_1101 v h)
                (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0846 A)
                  (nb090_wpp_notmem_0847 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v
                    (nb090_wpp_notmem_0848 A) (nb090_wpp_notmem_0849 v)
                    (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u
                      (nb090_wpp_notmem_0850 A) (nb090_wpp_notmem_0851 u)
                      (TEnvFresh.consFresh (nb090_alpha_dummy_003 A)
                        (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0852 A)
                        (nb090_wpp_notmem_0853 v u A h)
                        (TEnvFresh.nil ((syn_c2nd)).fv)))))))))))

@[expose]
noncomputable def nb090_wpp_refl_0124 (v : Var) (u : Var) (A : Class) (h : Var) :
    TReflOn
      [((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
        ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
        ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)),
        ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
        ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
        ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      ((syn_c2nd)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0124 v u A h)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
