/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block034

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part100`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0078`. -/
@[expose]
noncomputable def nb090SplitAlpha0078 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_h_v : h ≠ v) :
    TAlphaWff
      [((nb090AlphaDummy387 A), (nb090AlphaDummy388 v)),
        ((nb090AlphaDummy385 A), (nb090AlphaDummy386 v)),
        ((nb090AlphaDummy373 A), (nb090AlphaDummy374 v)),
        ((nb090AlphaDummy375 A), (nb090AlphaDummy376 v)),
        ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)),
        ((nb090AlphaDummy377 A), (nb090AlphaDummy379 v)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy387 A))
          (Class.cab (nb090AlphaDummy381 A)
            (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                (synCphi (Class.cv (nb090AlphaDummy382 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy387 A))
            (Class.cab (nb090AlphaDummy381 A)
              (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy002 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                  (synCphi (Class.cv (nb090AlphaDummy382 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy388 v))
          (Class.cab (nb090AlphaDummy383 v) (synWrex (nb090AlphaDummy384 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                (synCphi (Class.cv (nb090AlphaDummy384 v))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy388 v))
            (Class.cab (nb090AlphaDummy383 v)
              (synWrex (nb090AlphaDummy384 v) (Class.cv v)
                (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                  (synCphi (Class.cv (nb090AlphaDummy384 v))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy382 A) from (by
                      unfold nb090AlphaDummy382;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0392 A) 1))))
                  (show v ≠ (nb090AlphaDummy384 v) from (by
                      unfold nb090AlphaDummy384;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0394 v) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy381 A) from (by
                        unfold nb090AlphaDummy381;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0392 A) 0))))
                    (show v ≠ (nb090AlphaDummy383 v) from (by
                        unfold nb090AlphaDummy383;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0394 v) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy387 A) from (by
                          unfold nb090AlphaDummy387;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0396 A) 0))))
                      (show v ≠ (nb090AlphaDummy388 v) from (by
                          unfold nb090AlphaDummy388;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0397 v) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy385 A) from (by
                            unfold nb090AlphaDummy385;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0393 A) 0))))
                        (show v ≠ (nb090AlphaDummy386 v) from (by
                            unfold nb090AlphaDummy386;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0395 v) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy373 A) from (by
                              unfold nb090AlphaDummy373;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0386 A) 0))))
                          (show v ≠ (nb090AlphaDummy374 v) from (by
                              unfold nb090AlphaDummy374;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0389 v) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy375 A) from (by
                                unfold nb090AlphaDummy375;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0387 A) 0))))
                            (show v ≠ (nb090AlphaDummy376 v) from (by
                                unfold nb090AlphaDummy376;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0390 v) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy378 A) from
                                (by
                                  unfold nb090AlphaDummy378;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0388 A) 1))))
                              (show v ≠ (nb090AlphaDummy380 v) from (by
                                  unfold nb090AlphaDummy380;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0391 v) 1))))
                              (TAlphaVar.there (show
                                  (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy377 A) from (by
                                    unfold nb090AlphaDummy377;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0388 A)
                                            0)))) (show v ≠ (nb090AlphaDummy379 v) from (by
                                    unfold nb090AlphaDummy379;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0391 v)
                                            0))))
                                (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                  (Ne.symm dv_h_v) (TAlphaVar.here _ _ _))))))))))))
            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy002 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy373 A))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy374 v))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy382 A) ≠ (nb090AlphaDummy389 A) from (by
                              unfold nb090AlphaDummy389;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0398 A) 0))))
                          (show (nb090AlphaDummy384 v) ≠ (nb090AlphaDummy391 v) from (by
                              unfold nb090AlphaDummy391;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0399 v) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy382 A) ≠ (nb090AlphaDummy390 A) from (by
                                unfold nb090AlphaDummy390;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0398 A) 1))))
                            (show (nb090AlphaDummy384 v) ≠ (nb090AlphaDummy392 v) from (by
                                unfold nb090AlphaDummy392;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0399 v) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy382 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy384 v))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy396 A) from (by
          unfold nb090AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0402 A) 1)))) (show (nb090AlphaDummy391 v) ≠
        (nb090AlphaDummy399 v) from (by
          unfold nb090AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0403 v) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy395 A) from (by
          unfold nb090AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0402 A) 0)))) (show (nb090AlphaDummy391 v) ≠
        (nb090AlphaDummy398 v) from (by
          unfold nb090AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0403 v) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy393 A) from (by
          unfold nb090AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0400 A)
                  0)))) (show (nb090AlphaDummy391 v) ≠ (nb090AlphaDummy394 v) from (by
          unfold nb090AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0401 v)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy397 A), (nb090AlphaDummy400 v)), ((nb090AlphaDummy396 A),
        (nb090AlphaDummy399 v)), ((nb090AlphaDummy395 A), (nb090AlphaDummy398 v)),
        ((nb090AlphaDummy393 A), (nb090AlphaDummy394 v)), ((nb090AlphaDummy389 A),
        (nb090AlphaDummy391 v)), ((nb090AlphaDummy390 A), (nb090AlphaDummy392 v)),
        ((nb090AlphaDummy382 A), (nb090AlphaDummy384 v)), ((nb090AlphaDummy381 A),
        (nb090AlphaDummy383 v)), ((nb090AlphaDummy387 A), (nb090AlphaDummy388 v)),
        ((nb090AlphaDummy385 A), (nb090AlphaDummy386 v)), ((nb090AlphaDummy373 A),
        (nb090AlphaDummy374 v)), ((nb090AlphaDummy375 A), (nb090AlphaDummy376 v)),
        ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)), ((nb090AlphaDummy377 A),
        (nb090AlphaDummy379 v)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠ (nb090AlphaDummy403 A) from (by
          unfold
            nb090AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0406
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy404 v) from (by
          unfold
            nb090AlphaDummy404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0407
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠
        (nb090AlphaDummy401 A) from (by
          unfold
            nb090AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0404
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy402 v) from (by
          unfold
            nb090AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0405
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy389
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠ (nb090AlphaDummy403 A) from (by
          unfold
            nb090AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0410
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy404 v) from (by
          unfold
            nb090AlphaDummy404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0411
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠
        (nb090AlphaDummy401 A) from (by
          unfold
            nb090AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0408
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy402 v) from (by
          unfold
            nb090AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0409
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠ (nb090AlphaDummy403 A) from (by
          unfold
            nb090AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0406
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy404 v) from (by
          unfold
            nb090AlphaDummy404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0407
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠
        (nb090AlphaDummy401 A) from (by
          unfold
            nb090AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0404
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy402 v) from (by
          unfold
            nb090AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0405
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy389
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠ (nb090AlphaDummy403 A) from (by
          unfold
            nb090AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0410
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy404 v) from (by
          unfold
            nb090AlphaDummy404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0411
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠
        (nb090AlphaDummy401 A) from (by
          unfold
            nb090AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0408
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy402 v) from (by
          unfold
            nb090AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0409
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy397 A), (nb090AlphaDummy400 v)), ((nb090AlphaDummy396 A),
        (nb090AlphaDummy399 v)), ((nb090AlphaDummy395 A), (nb090AlphaDummy398 v)),
        ((nb090AlphaDummy393 A), (nb090AlphaDummy394 v)), ((nb090AlphaDummy389 A),
        (nb090AlphaDummy391 v)), ((nb090AlphaDummy390 A), (nb090AlphaDummy392 v)),
        ((nb090AlphaDummy382 A), (nb090AlphaDummy384 v)), ((nb090AlphaDummy381 A),
        (nb090AlphaDummy383 v)), ((nb090AlphaDummy387 A), (nb090AlphaDummy388 v)),
        ((nb090AlphaDummy385 A), (nb090AlphaDummy386 v)), ((nb090AlphaDummy373 A),
        (nb090AlphaDummy374 v)), ((nb090AlphaDummy375 A), (nb090AlphaDummy376 v)),
        ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)), ((nb090AlphaDummy377 A),
        (nb090AlphaDummy379 v)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy389 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy389 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy391 v))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy396
        A) ≠ (nb090AlphaDummy407 A) from (by
          unfold
            nb090AlphaDummy407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0414
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy408 v) from (by
          unfold
            nb090AlphaDummy408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0415
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠
        (nb090AlphaDummy405 A) from (by
          unfold
            nb090AlphaDummy405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0412
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy406 v) from (by
          unfold
            nb090AlphaDummy406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0413
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy389
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠ (nb090AlphaDummy407 A) from (by
          unfold
            nb090AlphaDummy407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0414
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy408 v) from (by
          unfold
            nb090AlphaDummy408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0415
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠
        (nb090AlphaDummy405 A) from (by
          unfold
            nb090AlphaDummy405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0412
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy406 v) from (by
          unfold
            nb090AlphaDummy406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0413
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy389
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy397
        A) ≠ (nb090AlphaDummy409 A) from (by
          unfold
            nb090AlphaDummy409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0418
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy410 v) from (by
          unfold
            nb090AlphaDummy410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0419
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠
        (nb090AlphaDummy405 A) from (by
          unfold
            nb090AlphaDummy405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0416
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy406 v) from (by
          unfold
            nb090AlphaDummy406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0417
                    v)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy397
        A) ≠ (nb090AlphaDummy409 A) from (by
          unfold
            nb090AlphaDummy409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0418
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy410 v) from (by
          unfold
            nb090AlphaDummy410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0419
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠
        (nb090AlphaDummy405 A) from (by
          unfold
            nb090AlphaDummy405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0416
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy406 v) from (by
          unfold
            nb090AlphaDummy406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0417
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy393 A) from
                                      (by
                                        unfold nb090AlphaDummy393;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0400 A)
                                                0)))) (show (nb090AlphaDummy391 v) ≠
                                        (nb090AlphaDummy394 v) from (by
                                        unfold nb090AlphaDummy394;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0401 v)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy393 A), (nb090AlphaDummy394 v)),
                                    ((nb090AlphaDummy389 A), (nb090AlphaDummy391 v)),
                                    ((nb090AlphaDummy390 A), (nb090AlphaDummy392 v)),
                                    ((nb090AlphaDummy382 A), (nb090AlphaDummy384 v)),
                                    ((nb090AlphaDummy381 A), (nb090AlphaDummy383 v)),
                                    ((nb090AlphaDummy387 A), (nb090AlphaDummy388 v)),
                                    ((nb090AlphaDummy385 A), (nb090AlphaDummy386 v)),
                                    ((nb090AlphaDummy373 A), (nb090AlphaDummy374 v)),
                                    ((nb090AlphaDummy375 A), (nb090AlphaDummy376 v)),
                                    ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)),
                                    ((nb090AlphaDummy377 A), (nb090AlphaDummy379 v)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy393 A) from
                                    (by
                                      unfold nb090AlphaDummy393;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0400 A)
                                              0)))) (show
                                    (nb090AlphaDummy391 v) ≠ (nb090AlphaDummy394 v) from
                                    (by
                                      unfold nb090AlphaDummy394;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0401 v)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy393 A) from
                                      (by
                                        unfold nb090AlphaDummy393;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0400 A)
                                                0)))) (show (nb090AlphaDummy391 v) ≠
                                        (nb090AlphaDummy394 v) from (by
                                        unfold nb090AlphaDummy394;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0401 v)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy393 A), (nb090AlphaDummy394 v)),
                                    ((nb090AlphaDummy389 A), (nb090AlphaDummy391 v)),
                                    ((nb090AlphaDummy390 A), (nb090AlphaDummy392 v)),
                                    ((nb090AlphaDummy382 A), (nb090AlphaDummy384 v)),
                                    ((nb090AlphaDummy381 A), (nb090AlphaDummy383 v)),
                                    ((nb090AlphaDummy387 A), (nb090AlphaDummy388 v)),
                                    ((nb090AlphaDummy385 A), (nb090AlphaDummy386 v)),
                                    ((nb090AlphaDummy373 A), (nb090AlphaDummy374 v)),
                                    ((nb090AlphaDummy375 A), (nb090AlphaDummy376 v)),
                                    ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)),
                                    ((nb090AlphaDummy377 A), (nb090AlphaDummy379 v)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy382 A) from (by
                        unfold nb090AlphaDummy382;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0392 A) 1))))
                    (show v ≠ (nb090AlphaDummy384 v) from (by
                        unfold nb090AlphaDummy384;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0394 v) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy381 A) from (by
                          unfold nb090AlphaDummy381;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0392 A) 0))))
                      (show v ≠ (nb090AlphaDummy383 v) from (by
                          unfold nb090AlphaDummy383;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0394 v) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy387 A) from (by
                            unfold nb090AlphaDummy387;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0396 A) 0))))
                        (show v ≠ (nb090AlphaDummy388 v) from (by
                            unfold nb090AlphaDummy388;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0397 v) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy385 A) from (by
                              unfold nb090AlphaDummy385;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0393 A) 0))))
                          (show v ≠ (nb090AlphaDummy386 v) from (by
                              unfold nb090AlphaDummy386;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0395 v) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy373 A) from (by
                                unfold nb090AlphaDummy373;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0386 A) 0))))
                            (show v ≠ (nb090AlphaDummy374 v) from (by
                                unfold nb090AlphaDummy374;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0389 v) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy375 A) from
                                (by
                                  unfold nb090AlphaDummy375;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0387 A) 0))))
                              (show v ≠ (nb090AlphaDummy376 v) from (by
                                  unfold nb090AlphaDummy376;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0390 v) 0))))
                              (TAlphaVar.there (show
                                  (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy378 A) from (by
                                    unfold nb090AlphaDummy378;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0388 A)
                                            1)))) (show v ≠ (nb090AlphaDummy380 v) from (by
                                    unfold nb090AlphaDummy380;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0391 v)
                                            1)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy377 A) from
                                    (by
                                      unfold nb090AlphaDummy377;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0388 A)
                                              0)))) (show v ≠ (nb090AlphaDummy379 v) from (by
                                      unfold nb090AlphaDummy379;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0391 v)
                                              0)))) (TAlphaVar.there
                                    (freshVar_injective ((A).fv) (by decide))
                                    (Ne.symm dv_h_v) (TAlphaVar.here _ _ _))))))))))))
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy002 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy373 A))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy374 v))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy382 A) ≠ (nb090AlphaDummy389 A) from (by
                                unfold nb090AlphaDummy389;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0398 A) 0))))
                            (show (nb090AlphaDummy384 v) ≠ (nb090AlphaDummy391 v) from (by
                                unfold nb090AlphaDummy391;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0399 v) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy382 A) ≠ (nb090AlphaDummy390 A) from
                                (by
                                  unfold nb090AlphaDummy390;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0398 A) 1))))
                              (show (nb090AlphaDummy384 v) ≠ (nb090AlphaDummy392 v) from
                                (by
                                  unfold nb090AlphaDummy392;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0399 v) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy382 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy384 v))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy396 A) from (by
          unfold nb090AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0402 A) 1)))) (show (nb090AlphaDummy391 v) ≠
        (nb090AlphaDummy399 v) from (by
          unfold nb090AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0403 v) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy395 A) from (by
          unfold nb090AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0402 A)
                  0)))) (show (nb090AlphaDummy391 v) ≠ (nb090AlphaDummy398 v) from (by
          unfold nb090AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0403 v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy389 A) ≠
        (nb090AlphaDummy393 A) from (by
          unfold nb090AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0400 A)
                  0)))) (show (nb090AlphaDummy391 v) ≠ (nb090AlphaDummy394 v) from (by
          unfold nb090AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0401 v)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy397 A), (nb090AlphaDummy400 v)), ((nb090AlphaDummy396 A),
        (nb090AlphaDummy399 v)), ((nb090AlphaDummy395 A), (nb090AlphaDummy398 v)),
        ((nb090AlphaDummy393 A), (nb090AlphaDummy394 v)), ((nb090AlphaDummy389 A),
        (nb090AlphaDummy391 v)), ((nb090AlphaDummy390 A), (nb090AlphaDummy392 v)),
        ((nb090AlphaDummy382 A), (nb090AlphaDummy384 v)), ((nb090AlphaDummy381 A),
        (nb090AlphaDummy383 v)), ((nb090AlphaDummy387 A), (nb090AlphaDummy388 v)),
        ((nb090AlphaDummy385 A), (nb090AlphaDummy386 v)), ((nb090AlphaDummy373 A),
        (nb090AlphaDummy374 v)), ((nb090AlphaDummy375 A), (nb090AlphaDummy376 v)),
        ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)), ((nb090AlphaDummy377 A),
        (nb090AlphaDummy379 v)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠ (nb090AlphaDummy403 A) from (by
          unfold
            nb090AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0406
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy404 v) from (by
          unfold
            nb090AlphaDummy404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0407
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠
        (nb090AlphaDummy401 A) from (by
          unfold
            nb090AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0404
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy402 v) from (by
          unfold
            nb090AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0405
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy389
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠ (nb090AlphaDummy403 A) from (by
          unfold
            nb090AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0410
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy404 v) from (by
          unfold
            nb090AlphaDummy404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0411
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠
        (nb090AlphaDummy401 A) from (by
          unfold
            nb090AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0408
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy402 v) from (by
          unfold
            nb090AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0409
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠ (nb090AlphaDummy403 A) from (by
          unfold
            nb090AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0406
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy404 v) from (by
          unfold
            nb090AlphaDummy404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0407
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠
        (nb090AlphaDummy401 A) from (by
          unfold
            nb090AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0404
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy402 v) from (by
          unfold
            nb090AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0405
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy389
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠ (nb090AlphaDummy403 A) from (by
          unfold
            nb090AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0410
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy404 v) from (by
          unfold
            nb090AlphaDummy404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0411
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠
        (nb090AlphaDummy401 A) from (by
          unfold
            nb090AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0408
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy402 v) from (by
          unfold
            nb090AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0409
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy397 A), (nb090AlphaDummy400 v)), ((nb090AlphaDummy396 A),
        (nb090AlphaDummy399 v)), ((nb090AlphaDummy395 A), (nb090AlphaDummy398 v)),
        ((nb090AlphaDummy393 A), (nb090AlphaDummy394 v)), ((nb090AlphaDummy389 A),
        (nb090AlphaDummy391 v)), ((nb090AlphaDummy390 A), (nb090AlphaDummy392 v)),
        ((nb090AlphaDummy382 A), (nb090AlphaDummy384 v)), ((nb090AlphaDummy381 A),
        (nb090AlphaDummy383 v)), ((nb090AlphaDummy387 A), (nb090AlphaDummy388 v)),
        ((nb090AlphaDummy385 A), (nb090AlphaDummy386 v)), ((nb090AlphaDummy373 A),
        (nb090AlphaDummy374 v)), ((nb090AlphaDummy375 A), (nb090AlphaDummy376 v)),
        ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)), ((nb090AlphaDummy377 A),
        (nb090AlphaDummy379 v)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy389 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy391
        v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy389 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy396
        A) ≠ (nb090AlphaDummy407 A) from (by
          unfold
            nb090AlphaDummy407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0414
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy408 v) from (by
          unfold
            nb090AlphaDummy408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0415
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠
        (nb090AlphaDummy405 A) from (by
          unfold
            nb090AlphaDummy405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0412
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy406 v) from (by
          unfold
            nb090AlphaDummy406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0413
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy389
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠ (nb090AlphaDummy407 A) from (by
          unfold
            nb090AlphaDummy407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0414
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy408 v) from (by
          unfold
            nb090AlphaDummy408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0415
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠
        (nb090AlphaDummy405 A) from (by
          unfold
            nb090AlphaDummy405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0412
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy406 v) from (by
          unfold
            nb090AlphaDummy406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0413
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy389
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy397
        A) ≠ (nb090AlphaDummy409 A) from (by
          unfold
            nb090AlphaDummy409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0418
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy410 v) from (by
          unfold
            nb090AlphaDummy410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0419
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠
        (nb090AlphaDummy405 A) from (by
          unfold
            nb090AlphaDummy405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0416
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy406 v) from (by
          unfold
            nb090AlphaDummy406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0417
                    v)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy397
        A) ≠ (nb090AlphaDummy409 A) from (by
          unfold
            nb090AlphaDummy409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0418
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy410 v) from (by
          unfold
            nb090AlphaDummy410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0419
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠
        (nb090AlphaDummy405 A) from (by
          unfold
            nb090AlphaDummy405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0416
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy406 v) from (by
          unfold
            nb090AlphaDummy406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0417
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy393 A)
                                        from (by
                                          unfold nb090AlphaDummy393;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0400 A) 0)))) (show
                                        (nb090AlphaDummy391 v) ≠ (nb090AlphaDummy394 v)
                                        from (by
                                          unfold nb090AlphaDummy394;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0401 v) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy393 A), (nb090AlphaDummy394 v)),
                                      ((nb090AlphaDummy389 A), (nb090AlphaDummy391 v)),
                                      ((nb090AlphaDummy390 A), (nb090AlphaDummy392 v)),
                                      ((nb090AlphaDummy382 A), (nb090AlphaDummy384 v)),
                                      ((nb090AlphaDummy381 A), (nb090AlphaDummy383 v)),
                                      ((nb090AlphaDummy387 A), (nb090AlphaDummy388 v)),
                                      ((nb090AlphaDummy385 A), (nb090AlphaDummy386 v)),
                                      ((nb090AlphaDummy373 A), (nb090AlphaDummy374 v)),
                                      ((nb090AlphaDummy375 A), (nb090AlphaDummy376 v)),
                                      ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)),
                                      ((nb090AlphaDummy377 A), (nb090AlphaDummy379 v)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy393 A) from
                                      (by
                                        unfold nb090AlphaDummy393;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0400 A)
                                                0)))) (show (nb090AlphaDummy391 v) ≠
                                        (nb090AlphaDummy394 v) from (by
                                        unfold nb090AlphaDummy394;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0401 v)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy393 A)
                                        from (by
                                          unfold nb090AlphaDummy393;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0400 A) 0)))) (show
                                        (nb090AlphaDummy391 v) ≠ (nb090AlphaDummy394 v)
                                        from (by
                                          unfold nb090AlphaDummy394;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0401 v) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy393 A), (nb090AlphaDummy394 v)),
                                      ((nb090AlphaDummy389 A), (nb090AlphaDummy391 v)),
                                      ((nb090AlphaDummy390 A), (nb090AlphaDummy392 v)),
                                      ((nb090AlphaDummy382 A), (nb090AlphaDummy384 v)),
                                      ((nb090AlphaDummy381 A), (nb090AlphaDummy383 v)),
                                      ((nb090AlphaDummy387 A), (nb090AlphaDummy388 v)),
                                      ((nb090AlphaDummy385 A), (nb090AlphaDummy386 v)),
                                      ((nb090AlphaDummy373 A), (nb090AlphaDummy374 v)),
                                      ((nb090AlphaDummy375 A), (nb090AlphaDummy376 v)),
                                      ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)),
                                      ((nb090AlphaDummy377 A), (nb090AlphaDummy379 v)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part101`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0079`. -/
@[expose]
noncomputable def nb090SplitAlpha0079 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy413 A), (nb090AlphaDummy414 v)),
        ((nb090AlphaDummy382 A), (nb090AlphaDummy384 v)),
        ((nb090AlphaDummy381 A), (nb090AlphaDummy383 v)),
        ((nb090AlphaDummy411 A), (nb090AlphaDummy412 v)),
        ((nb090AlphaDummy385 A), (nb090AlphaDummy386 v)),
        ((nb090AlphaDummy373 A), (nb090AlphaDummy374 v)),
        ((nb090AlphaDummy375 A), (nb090AlphaDummy376 v)),
        ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)),
        ((nb090AlphaDummy377 A), (nb090AlphaDummy379 v)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy413 A))
          (synCcompl (synCphi (Class.cv (nb090AlphaDummy382 A))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy413 A)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy414 v))
          (synCcompl (synCphi (Class.cv (nb090AlphaDummy384 v))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy414 v))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy382 A) ≠ (nb090AlphaDummy389 A) from (by
                              unfold nb090AlphaDummy389;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0398 A) 0))))
                          (show (nb090AlphaDummy384 v) ≠ (nb090AlphaDummy391 v) from (by
                              unfold nb090AlphaDummy391;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0399 v) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy382 A) ≠ (nb090AlphaDummy390 A) from (by
                                unfold nb090AlphaDummy390;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0398 A) 1))))
                            (show (nb090AlphaDummy384 v) ≠ (nb090AlphaDummy392 v) from (by
                                unfold nb090AlphaDummy392;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0399 v) 1))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy382 A) ≠ (nb090AlphaDummy415 A) from
                                (by
                                  unfold nb090AlphaDummy415;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0428 A) 0))))
                              (show (nb090AlphaDummy384 v) ≠ (nb090AlphaDummy416 v) from
                                (by
                                  unfold nb090AlphaDummy416;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0429 v) 0))))
                              (TAlphaVar.there (show
                                  (nb090AlphaDummy382 A) ≠ (nb090AlphaDummy413 A) from (by
                                    unfold nb090AlphaDummy413;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0426 A)
                                            0)))) (show
                                  (nb090AlphaDummy384 v) ≠ (nb090AlphaDummy414 v) from (by
                                    unfold nb090AlphaDummy414;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0427 v)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy382 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy384 v))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy396 A) from (by
          unfold nb090AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0402 A) 1)))) (show (nb090AlphaDummy391 v) ≠
        (nb090AlphaDummy399 v) from (by
          unfold nb090AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0403 v) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy395 A) from (by
          unfold nb090AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0402 A) 0)))) (show (nb090AlphaDummy391 v) ≠
        (nb090AlphaDummy398 v) from (by
          unfold nb090AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0403 v) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy393 A) from (by
          unfold nb090AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0400 A)
                  0)))) (show (nb090AlphaDummy391 v) ≠ (nb090AlphaDummy394 v) from (by
          unfold nb090AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0401 v)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy397 A), (nb090AlphaDummy400 v)), ((nb090AlphaDummy396 A),
        (nb090AlphaDummy399 v)), ((nb090AlphaDummy395 A), (nb090AlphaDummy398 v)),
        ((nb090AlphaDummy393 A), (nb090AlphaDummy394 v)), ((nb090AlphaDummy389 A),
        (nb090AlphaDummy391 v)), ((nb090AlphaDummy390 A), (nb090AlphaDummy392 v)),
        ((nb090AlphaDummy415 A), (nb090AlphaDummy416 v)), ((nb090AlphaDummy413 A),
        (nb090AlphaDummy414 v)), ((nb090AlphaDummy382 A), (nb090AlphaDummy384 v)),
        ((nb090AlphaDummy381 A), (nb090AlphaDummy383 v)), ((nb090AlphaDummy411 A),
        (nb090AlphaDummy412 v)), ((nb090AlphaDummy385 A), (nb090AlphaDummy386 v)),
        ((nb090AlphaDummy373 A), (nb090AlphaDummy374 v)), ((nb090AlphaDummy375 A),
        (nb090AlphaDummy376 v)), ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)),
        ((nb090AlphaDummy377 A), (nb090AlphaDummy379 v)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠ (nb090AlphaDummy403 A) from (by
          unfold
            nb090AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0406
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy404 v) from (by
          unfold
            nb090AlphaDummy404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0407
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠
        (nb090AlphaDummy401 A) from (by
          unfold
            nb090AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0404
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy402 v) from (by
          unfold
            nb090AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0405
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy389
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠ (nb090AlphaDummy403 A) from (by
          unfold
            nb090AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0410
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy404 v) from (by
          unfold
            nb090AlphaDummy404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0411
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠
        (nb090AlphaDummy401 A) from (by
          unfold
            nb090AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0408
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy402 v) from (by
          unfold
            nb090AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0409
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠ (nb090AlphaDummy403 A) from (by
          unfold
            nb090AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0406
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy404 v) from (by
          unfold
            nb090AlphaDummy404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0407
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠
        (nb090AlphaDummy401 A) from (by
          unfold
            nb090AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0404
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy402 v) from (by
          unfold
            nb090AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0405
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy389
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠ (nb090AlphaDummy403 A) from (by
          unfold
            nb090AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0410
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy404 v) from (by
          unfold
            nb090AlphaDummy404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0411
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠
        (nb090AlphaDummy401 A) from (by
          unfold
            nb090AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0408
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy402 v) from (by
          unfold
            nb090AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0409
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy397 A), (nb090AlphaDummy400 v)), ((nb090AlphaDummy396 A),
        (nb090AlphaDummy399 v)), ((nb090AlphaDummy395 A), (nb090AlphaDummy398 v)),
        ((nb090AlphaDummy393 A), (nb090AlphaDummy394 v)), ((nb090AlphaDummy389 A),
        (nb090AlphaDummy391 v)), ((nb090AlphaDummy390 A), (nb090AlphaDummy392 v)),
        ((nb090AlphaDummy415 A), (nb090AlphaDummy416 v)), ((nb090AlphaDummy413 A),
        (nb090AlphaDummy414 v)), ((nb090AlphaDummy382 A), (nb090AlphaDummy384 v)),
        ((nb090AlphaDummy381 A), (nb090AlphaDummy383 v)), ((nb090AlphaDummy411 A),
        (nb090AlphaDummy412 v)), ((nb090AlphaDummy385 A), (nb090AlphaDummy386 v)),
        ((nb090AlphaDummy373 A), (nb090AlphaDummy374 v)), ((nb090AlphaDummy375 A),
        (nb090AlphaDummy376 v)), ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)),
        ((nb090AlphaDummy377 A), (nb090AlphaDummy379 v)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy389 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy389 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy391 v))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy396
        A) ≠ (nb090AlphaDummy407 A) from (by
          unfold
            nb090AlphaDummy407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0414
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy408 v) from (by
          unfold
            nb090AlphaDummy408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0415
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠
        (nb090AlphaDummy405 A) from (by
          unfold
            nb090AlphaDummy405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0412
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy406 v) from (by
          unfold
            nb090AlphaDummy406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0413
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy389
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠ (nb090AlphaDummy407 A) from (by
          unfold
            nb090AlphaDummy407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0414
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy408 v) from (by
          unfold
            nb090AlphaDummy408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0415
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠
        (nb090AlphaDummy405 A) from (by
          unfold
            nb090AlphaDummy405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0412
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy406 v) from (by
          unfold
            nb090AlphaDummy406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0413
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy389
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy397
        A) ≠ (nb090AlphaDummy409 A) from (by
          unfold
            nb090AlphaDummy409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0418
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy410 v) from (by
          unfold
            nb090AlphaDummy410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0419
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠
        (nb090AlphaDummy405 A) from (by
          unfold
            nb090AlphaDummy405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0416
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy406 v) from (by
          unfold
            nb090AlphaDummy406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0417
                    v)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy397
        A) ≠ (nb090AlphaDummy409 A) from (by
          unfold
            nb090AlphaDummy409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0418
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy410 v) from (by
          unfold
            nb090AlphaDummy410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0419
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠
        (nb090AlphaDummy405 A) from (by
          unfold
            nb090AlphaDummy405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0416
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy406 v) from (by
          unfold
            nb090AlphaDummy406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0417
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy393 A) from
                                      (by
                                        unfold nb090AlphaDummy393;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0400 A)
                                                0)))) (show (nb090AlphaDummy391 v) ≠
                                        (nb090AlphaDummy394 v) from (by
                                        unfold nb090AlphaDummy394;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0401 v)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy393 A), (nb090AlphaDummy394 v)),
                                    ((nb090AlphaDummy389 A), (nb090AlphaDummy391 v)),
                                    ((nb090AlphaDummy390 A), (nb090AlphaDummy392 v)),
                                    ((nb090AlphaDummy415 A), (nb090AlphaDummy416 v)),
                                    ((nb090AlphaDummy413 A), (nb090AlphaDummy414 v)),
                                    ((nb090AlphaDummy382 A), (nb090AlphaDummy384 v)),
                                    ((nb090AlphaDummy381 A), (nb090AlphaDummy383 v)),
                                    ((nb090AlphaDummy411 A), (nb090AlphaDummy412 v)),
                                    ((nb090AlphaDummy385 A), (nb090AlphaDummy386 v)),
                                    ((nb090AlphaDummy373 A), (nb090AlphaDummy374 v)),
                                    ((nb090AlphaDummy375 A), (nb090AlphaDummy376 v)),
                                    ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)),
                                    ((nb090AlphaDummy377 A), (nb090AlphaDummy379 v)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy393 A) from
                                    (by
                                      unfold nb090AlphaDummy393;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0400 A)
                                              0)))) (show
                                    (nb090AlphaDummy391 v) ≠ (nb090AlphaDummy394 v) from
                                    (by
                                      unfold nb090AlphaDummy394;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0401 v)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy393 A) from
                                      (by
                                        unfold nb090AlphaDummy393;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0400 A)
                                                0)))) (show (nb090AlphaDummy391 v) ≠
                                        (nb090AlphaDummy394 v) from (by
                                        unfold nb090AlphaDummy394;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0401 v)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy393 A), (nb090AlphaDummy394 v)),
                                    ((nb090AlphaDummy389 A), (nb090AlphaDummy391 v)),
                                    ((nb090AlphaDummy390 A), (nb090AlphaDummy392 v)),
                                    ((nb090AlphaDummy415 A), (nb090AlphaDummy416 v)),
                                    ((nb090AlphaDummy413 A), (nb090AlphaDummy414 v)),
                                    ((nb090AlphaDummy382 A), (nb090AlphaDummy384 v)),
                                    ((nb090AlphaDummy381 A), (nb090AlphaDummy383 v)),
                                    ((nb090AlphaDummy411 A), (nb090AlphaDummy412 v)),
                                    ((nb090AlphaDummy385 A), (nb090AlphaDummy386 v)),
                                    ((nb090AlphaDummy373 A), (nb090AlphaDummy374 v)),
                                    ((nb090AlphaDummy375 A), (nb090AlphaDummy376 v)),
                                    ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)),
                                    ((nb090AlphaDummy377 A), (nb090AlphaDummy379 v)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy382 A) ≠ (nb090AlphaDummy389 A) from (by
                              unfold nb090AlphaDummy389;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0398 A) 0))))
                          (show (nb090AlphaDummy384 v) ≠ (nb090AlphaDummy391 v) from (by
                              unfold nb090AlphaDummy391;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0399 v) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy382 A) ≠ (nb090AlphaDummy390 A) from (by
                                unfold nb090AlphaDummy390;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0398 A) 1))))
                            (show (nb090AlphaDummy384 v) ≠ (nb090AlphaDummy392 v) from (by
                                unfold nb090AlphaDummy392;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0399 v) 1))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy382 A) ≠ (nb090AlphaDummy415 A) from
                                (by
                                  unfold nb090AlphaDummy415;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0428 A) 0))))
                              (show (nb090AlphaDummy384 v) ≠ (nb090AlphaDummy416 v) from
                                (by
                                  unfold nb090AlphaDummy416;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0429 v) 0))))
                              (TAlphaVar.there (show
                                  (nb090AlphaDummy382 A) ≠ (nb090AlphaDummy413 A) from (by
                                    unfold nb090AlphaDummy413;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0426 A)
                                            0)))) (show
                                  (nb090AlphaDummy384 v) ≠ (nb090AlphaDummy414 v) from (by
                                    unfold nb090AlphaDummy414;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0427 v)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy382 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy384 v))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy396 A) from (by
          unfold nb090AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0402 A) 1)))) (show (nb090AlphaDummy391 v) ≠
        (nb090AlphaDummy399 v) from (by
          unfold nb090AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0403 v) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy395 A) from (by
          unfold nb090AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0402 A) 0)))) (show (nb090AlphaDummy391 v) ≠
        (nb090AlphaDummy398 v) from (by
          unfold nb090AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0403 v) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy393 A) from (by
          unfold nb090AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0400 A)
                  0)))) (show (nb090AlphaDummy391 v) ≠ (nb090AlphaDummy394 v) from (by
          unfold nb090AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0401 v)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy397 A), (nb090AlphaDummy400 v)), ((nb090AlphaDummy396 A),
        (nb090AlphaDummy399 v)), ((nb090AlphaDummy395 A), (nb090AlphaDummy398 v)),
        ((nb090AlphaDummy393 A), (nb090AlphaDummy394 v)), ((nb090AlphaDummy389 A),
        (nb090AlphaDummy391 v)), ((nb090AlphaDummy390 A), (nb090AlphaDummy392 v)),
        ((nb090AlphaDummy415 A), (nb090AlphaDummy416 v)), ((nb090AlphaDummy413 A),
        (nb090AlphaDummy414 v)), ((nb090AlphaDummy382 A), (nb090AlphaDummy384 v)),
        ((nb090AlphaDummy381 A), (nb090AlphaDummy383 v)), ((nb090AlphaDummy411 A),
        (nb090AlphaDummy412 v)), ((nb090AlphaDummy385 A), (nb090AlphaDummy386 v)),
        ((nb090AlphaDummy373 A), (nb090AlphaDummy374 v)), ((nb090AlphaDummy375 A),
        (nb090AlphaDummy376 v)), ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)),
        ((nb090AlphaDummy377 A), (nb090AlphaDummy379 v)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠ (nb090AlphaDummy403 A) from (by
          unfold
            nb090AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0406
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy404 v) from (by
          unfold
            nb090AlphaDummy404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0407
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠
        (nb090AlphaDummy401 A) from (by
          unfold
            nb090AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0404
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy402 v) from (by
          unfold
            nb090AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0405
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy389
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠ (nb090AlphaDummy403 A) from (by
          unfold
            nb090AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0410
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy404 v) from (by
          unfold
            nb090AlphaDummy404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0411
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠
        (nb090AlphaDummy401 A) from (by
          unfold
            nb090AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0408
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy402 v) from (by
          unfold
            nb090AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0409
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠ (nb090AlphaDummy403 A) from (by
          unfold
            nb090AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0406
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy404 v) from (by
          unfold
            nb090AlphaDummy404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0407
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠
        (nb090AlphaDummy401 A) from (by
          unfold
            nb090AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0404
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy402 v) from (by
          unfold
            nb090AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0405
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy389
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠ (nb090AlphaDummy403 A) from (by
          unfold
            nb090AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0410
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy404 v) from (by
          unfold
            nb090AlphaDummy404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0411
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠
        (nb090AlphaDummy401 A) from (by
          unfold
            nb090AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0408
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy402 v) from (by
          unfold
            nb090AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0409
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy397 A), (nb090AlphaDummy400 v)), ((nb090AlphaDummy396 A),
        (nb090AlphaDummy399 v)), ((nb090AlphaDummy395 A), (nb090AlphaDummy398 v)),
        ((nb090AlphaDummy393 A), (nb090AlphaDummy394 v)), ((nb090AlphaDummy389 A),
        (nb090AlphaDummy391 v)), ((nb090AlphaDummy390 A), (nb090AlphaDummy392 v)),
        ((nb090AlphaDummy415 A), (nb090AlphaDummy416 v)), ((nb090AlphaDummy413 A),
        (nb090AlphaDummy414 v)), ((nb090AlphaDummy382 A), (nb090AlphaDummy384 v)),
        ((nb090AlphaDummy381 A), (nb090AlphaDummy383 v)), ((nb090AlphaDummy411 A),
        (nb090AlphaDummy412 v)), ((nb090AlphaDummy385 A), (nb090AlphaDummy386 v)),
        ((nb090AlphaDummy373 A), (nb090AlphaDummy374 v)), ((nb090AlphaDummy375 A),
        (nb090AlphaDummy376 v)), ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)),
        ((nb090AlphaDummy377 A), (nb090AlphaDummy379 v)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy389 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy389 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy391 v))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy396
        A) ≠ (nb090AlphaDummy407 A) from (by
          unfold
            nb090AlphaDummy407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0414
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy408 v) from (by
          unfold
            nb090AlphaDummy408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0415
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠
        (nb090AlphaDummy405 A) from (by
          unfold
            nb090AlphaDummy405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0412
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy406 v) from (by
          unfold
            nb090AlphaDummy406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0413
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy389
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠ (nb090AlphaDummy407 A) from (by
          unfold
            nb090AlphaDummy407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0414
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy408 v) from (by
          unfold
            nb090AlphaDummy408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0415
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy396 A) ≠
        (nb090AlphaDummy405 A) from (by
          unfold
            nb090AlphaDummy405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0412
                    A)
                  0)))) (show (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy406 v) from (by
          unfold
            nb090AlphaDummy406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0413
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy389
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy397
        A) ≠ (nb090AlphaDummy409 A) from (by
          unfold
            nb090AlphaDummy409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0418
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy410 v) from (by
          unfold
            nb090AlphaDummy410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0419
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠
        (nb090AlphaDummy405 A) from (by
          unfold
            nb090AlphaDummy405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0416
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy406 v) from (by
          unfold
            nb090AlphaDummy406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0417
                    v)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy397
        A) ≠ (nb090AlphaDummy409 A) from (by
          unfold
            nb090AlphaDummy409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0418
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy410 v) from (by
          unfold
            nb090AlphaDummy410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0419
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy397 A) ≠
        (nb090AlphaDummy405 A) from (by
          unfold
            nb090AlphaDummy405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0416
                    A)
                  0)))) (show (nb090AlphaDummy400 v) ≠ (nb090AlphaDummy406 v) from (by
          unfold
            nb090AlphaDummy406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0417
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy393 A) from
                                      (by
                                        unfold nb090AlphaDummy393;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0400 A)
                                                0)))) (show (nb090AlphaDummy391 v) ≠
                                        (nb090AlphaDummy394 v) from (by
                                        unfold nb090AlphaDummy394;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0401 v)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy393 A), (nb090AlphaDummy394 v)),
                                    ((nb090AlphaDummy389 A), (nb090AlphaDummy391 v)),
                                    ((nb090AlphaDummy390 A), (nb090AlphaDummy392 v)),
                                    ((nb090AlphaDummy415 A), (nb090AlphaDummy416 v)),
                                    ((nb090AlphaDummy413 A), (nb090AlphaDummy414 v)),
                                    ((nb090AlphaDummy382 A), (nb090AlphaDummy384 v)),
                                    ((nb090AlphaDummy381 A), (nb090AlphaDummy383 v)),
                                    ((nb090AlphaDummy411 A), (nb090AlphaDummy412 v)),
                                    ((nb090AlphaDummy385 A), (nb090AlphaDummy386 v)),
                                    ((nb090AlphaDummy373 A), (nb090AlphaDummy374 v)),
                                    ((nb090AlphaDummy375 A), (nb090AlphaDummy376 v)),
                                    ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)),
                                    ((nb090AlphaDummy377 A), (nb090AlphaDummy379 v)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy393 A) from
                                    (by
                                      unfold nb090AlphaDummy393;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0400 A)
                                              0)))) (show
                                    (nb090AlphaDummy391 v) ≠ (nb090AlphaDummy394 v) from
                                    (by
                                      unfold nb090AlphaDummy394;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0401 v)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy393 A) from
                                      (by
                                        unfold nb090AlphaDummy393;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0400 A)
                                                0)))) (show (nb090AlphaDummy391 v) ≠
                                        (nb090AlphaDummy394 v) from (by
                                        unfold nb090AlphaDummy394;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0401 v)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy393 A), (nb090AlphaDummy394 v)),
                                    ((nb090AlphaDummy389 A), (nb090AlphaDummy391 v)),
                                    ((nb090AlphaDummy390 A), (nb090AlphaDummy392 v)),
                                    ((nb090AlphaDummy415 A), (nb090AlphaDummy416 v)),
                                    ((nb090AlphaDummy413 A), (nb090AlphaDummy414 v)),
                                    ((nb090AlphaDummy382 A), (nb090AlphaDummy384 v)),
                                    ((nb090AlphaDummy381 A), (nb090AlphaDummy383 v)),
                                    ((nb090AlphaDummy411 A), (nb090AlphaDummy412 v)),
                                    ((nb090AlphaDummy385 A), (nb090AlphaDummy386 v)),
                                    ((nb090AlphaDummy373 A), (nb090AlphaDummy374 v)),
                                    ((nb090AlphaDummy375 A), (nb090AlphaDummy376 v)),
                                    ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)),
                                    ((nb090AlphaDummy377 A), (nb090AlphaDummy379 v)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb090AlphaDummy413 A), (nb090AlphaDummy414 v)),
            ((nb090AlphaDummy382 A), (nb090AlphaDummy384 v)),
            ((nb090AlphaDummy381 A), (nb090AlphaDummy383 v)),
            ((nb090AlphaDummy411 A), (nb090AlphaDummy412 v)),
            ((nb090AlphaDummy385 A), (nb090AlphaDummy386 v)),
            ((nb090AlphaDummy373 A), (nb090AlphaDummy374 v)),
            ((nb090AlphaDummy375 A), (nb090AlphaDummy376 v)),
            ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)),
            ((nb090AlphaDummy377 A), (nb090AlphaDummy379 v)),
            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
            ((nb090AlphaDummy001 A), u),
            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
          (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

theorem nb090_compact_envfresh_0267 (v : Var) (u : Var) (A : Class) (h : Var) :
    TEnvFresh
      [((nb090AlphaDummy373 A), (nb090AlphaDummy374 v)),
        ((nb090AlphaDummy375 A), (nb090AlphaDummy376 v)),
        ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)),
        ((nb090AlphaDummy377 A), (nb090AlphaDummy379 v)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      ((synC2nd)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb090AlphaDummy373 A) (nb090AlphaDummy374 v)
      (nb090_wpp_notmem_1090 A) (nb090_wpp_notmem_1091 v)
      (TEnvFresh.consFresh (nb090AlphaDummy375 A) (nb090AlphaDummy376 v)
        (nb090_wpp_notmem_1092 A) (nb090_wpp_notmem_1093 v)
        (TEnvFresh.consFresh (nb090AlphaDummy378 A) (nb090AlphaDummy380 v)
          (nb090_wpp_notmem_1094 A) (nb090_wpp_notmem_1095 v)
          (TEnvFresh.consFresh (nb090AlphaDummy377 A) (nb090AlphaDummy379 v)
            (nb090_wpp_notmem_1096 A) (nb090_wpp_notmem_1097 v)
            (TEnvFresh.consFresh (nb090AlphaDummy000 A) h (nb090_wpp_notmem_0846 A)
              (nb090_wpp_notmem_0847 h)
              (TEnvFresh.consFresh (nb090AlphaDummy002 A) v (nb090_wpp_notmem_0848 A)
                (nb090_wpp_notmem_0849 v)
                (TEnvFresh.consFresh (nb090AlphaDummy001 A) u (nb090_wpp_notmem_0850 A)
                  (nb090_wpp_notmem_0851 u) (TEnvFresh.consFresh (nb090AlphaDummy003 A)
                    (nb090AlphaDummy004 v u A h) (nb090_wpp_notmem_0852 A)
                    (nb090_wpp_notmem_0853 v u A h) (TEnvFresh.nil ((synC2nd)).fv)))))))))

/-- Checked nominal proof certificate identified upstream as `nb090_wpp_refl_0267`. -/
@[expose]
noncomputable def nb090WppRefl0267 (v : Var) (u : Var) (A : Class) (h : Var) :
    TReflOn
      [((nb090AlphaDummy373 A), (nb090AlphaDummy374 v)),
        ((nb090AlphaDummy375 A), (nb090AlphaDummy376 v)),
        ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)),
        ((nb090AlphaDummy377 A), (nb090AlphaDummy379 v)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      ((synC2nd)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0267 v u A h)

theorem nb090_compact_fv_empty_0462 (A : Class) :
    (nb090AlphaDummy041 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0463 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy043 v u h) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
