/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part023

/-! NF weak partition development: NAR4H5C095M3Part024. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0043`. -/
@[expose]
noncomputable def nb095SplitAlpha0043 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy513 D R S_cls E), (nb095AlphaDummy514 f)),
        ((nb095AlphaDummy511 D R S_cls E), (nb095AlphaDummy512 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy513 D R S_cls E))
          (Class.cab (nb095AlphaDummy507 D R S_cls E)
            (synWrex (nb095AlphaDummy508 D R S_cls E)
              (Class.cv (nb095AlphaDummy466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy513 D R S_cls E))
            (Class.cab (nb095AlphaDummy507 D R S_cls E)
              (synWrex (nb095AlphaDummy508 D R S_cls E)
                (Class.cv (nb095AlphaDummy466 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy514 f))
          (Class.cab (nb095AlphaDummy509 f)
            (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy468 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                (synCphi (Class.cv (nb095AlphaDummy510 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy514 f))
            (Class.cab (nb095AlphaDummy509 f)
              (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy468 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                  (synCphi (Class.cv (nb095AlphaDummy510 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy466 D R S_cls E) ≠
                      (nb095AlphaDummy508 D R S_cls E) from (by
                      unfold nb095AlphaDummy508;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0512 D R S_cls E) 1))))
                  (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy510 f) from (by
                      unfold nb095AlphaDummy510;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0514 f) 1))))
                  (TAlphaVar.there (show (nb095AlphaDummy466 D R S_cls E) ≠
                        (nb095AlphaDummy507 D R S_cls E) from (by
                        unfold nb095AlphaDummy507;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0512 D R S_cls E) 0))))
                    (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy509 f) from (by
                        unfold nb095AlphaDummy509;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0514 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy466 D R S_cls E) ≠
                          (nb095AlphaDummy513 D R S_cls E) from (by
                          unfold nb095AlphaDummy513;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0516 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy514 f) from (by
                          unfold nb095AlphaDummy514;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0517 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy466 D R S_cls E) ≠
                            (nb095AlphaDummy511 D R S_cls E) from (by
                            unfold nb095AlphaDummy511;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0513 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy512 f) from (by
                            unfold nb095AlphaDummy512;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0515 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy468 f))).fv ∪
                      ((Class.cv (nb095AlphaDummy467 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy508 D R S_cls E) ≠
                              (nb095AlphaDummy515 D R S_cls E) from (by
                              unfold nb095AlphaDummy515;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0518 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy510 f) ≠ (nb095AlphaDummy517 f) from (by
                              unfold nb095AlphaDummy517;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0519 f) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy508 D R S_cls E) ≠
                                (nb095AlphaDummy516 D R S_cls E) from (by
                                unfold nb095AlphaDummy516;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0518 D R S_cls E) 1))))
                            (show (nb095AlphaDummy510 f) ≠ (nb095AlphaDummy518 f) from (by
                                unfold nb095AlphaDummy518;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0519 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy508 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy510 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy515 D R S_cls E) ≠
        (nb095AlphaDummy522 D R S_cls E) from (by
          unfold nb095AlphaDummy522;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0522 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy525 f) from (by
          unfold nb095AlphaDummy525;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0523 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy515 D R S_cls E) ≠ (nb095AlphaDummy521 D R S_cls E) from (by
          unfold nb095AlphaDummy521;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0522 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy524 f) from (by
          unfold nb095AlphaDummy524;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0523 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy515 D R S_cls E) ≠ (nb095AlphaDummy519 D R S_cls E) from (by
          unfold nb095AlphaDummy519;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0520 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy520 f) from (by
          unfold nb095AlphaDummy520;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0521 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy523 D R S_cls E), (nb095AlphaDummy526 f)),
        ((nb095AlphaDummy522 D R S_cls E), (nb095AlphaDummy525 f)),
        ((nb095AlphaDummy521 D R S_cls E), (nb095AlphaDummy524 f)),
        ((nb095AlphaDummy519 D R S_cls E), (nb095AlphaDummy520 f)),
        ((nb095AlphaDummy515 D R S_cls E), (nb095AlphaDummy517 f)),
        ((nb095AlphaDummy516 D R S_cls E), (nb095AlphaDummy518 f)),
        ((nb095AlphaDummy508 D R S_cls E), (nb095AlphaDummy510 f)),
        ((nb095AlphaDummy507 D R S_cls E), (nb095AlphaDummy509 f)),
        ((nb095AlphaDummy513 D R S_cls E), (nb095AlphaDummy514 f)),
        ((nb095AlphaDummy511 D R S_cls E), (nb095AlphaDummy512 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy522
        D R S_cls E) ≠ (nb095AlphaDummy529 D R S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0526
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0527
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0524
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0525
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠ (nb095AlphaDummy529
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0530
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0531
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0528
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0529
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠ (nb095AlphaDummy529
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0526
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0527
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0524
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0525
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠ (nb095AlphaDummy529
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0530
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0531
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0528
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0529
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy523 D R S_cls E), (nb095AlphaDummy526 f)),
        ((nb095AlphaDummy522 D R S_cls E), (nb095AlphaDummy525 f)),
        ((nb095AlphaDummy521 D R S_cls E), (nb095AlphaDummy524 f)),
        ((nb095AlphaDummy519 D R S_cls E), (nb095AlphaDummy520 f)),
        ((nb095AlphaDummy515 D R S_cls E), (nb095AlphaDummy517 f)),
        ((nb095AlphaDummy516 D R S_cls E), (nb095AlphaDummy518 f)),
        ((nb095AlphaDummy508 D R S_cls E), (nb095AlphaDummy510 f)),
        ((nb095AlphaDummy507 D R S_cls E), (nb095AlphaDummy509 f)),
        ((nb095AlphaDummy513 D R S_cls E), (nb095AlphaDummy514 f)),
        ((nb095AlphaDummy511 D R S_cls E), (nb095AlphaDummy512 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy515 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠ (nb095AlphaDummy533
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0534
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy534 f) from (by
          unfold
            nb095AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0535
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0532
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0533
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠ (nb095AlphaDummy533
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0534
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy534 f) from (by
          unfold
            nb095AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0535
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0532
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0533
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy523
        D R S_cls E) ≠ (nb095AlphaDummy535 D R S_cls E) from (by
          unfold
            nb095AlphaDummy535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0538
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy536 f) from (by
          unfold
            nb095AlphaDummy536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0539
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0536
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0537
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy523
        D R S_cls E) ≠ (nb095AlphaDummy535 D R S_cls E) from (by
          unfold
            nb095AlphaDummy535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0538
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy536 f) from (by
          unfold
            nb095AlphaDummy536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0539
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0536
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0537
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy515 D R S_cls E) ≠
                                        (nb095AlphaDummy519 D R S_cls E) from (by
                                        unfold nb095AlphaDummy519;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0520 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy520 f) from
                                      (by
                                        unfold nb095AlphaDummy520;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0521 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy519 D R S_cls E),
                                      (nb095AlphaDummy520 f)),
                                    ((nb095AlphaDummy515 D R S_cls E),
                                      (nb095AlphaDummy517 f)),
                                    ((nb095AlphaDummy516 D R S_cls E),
                                      (nb095AlphaDummy518 f)),
                                    ((nb095AlphaDummy508 D R S_cls E),
                                      (nb095AlphaDummy510 f)),
                                    ((nb095AlphaDummy507 D R S_cls E),
                                      (nb095AlphaDummy509 f)),
                                    ((nb095AlphaDummy513 D R S_cls E),
                                      (nb095AlphaDummy514 f)),
                                    ((nb095AlphaDummy511 D R S_cls E),
                                      (nb095AlphaDummy512 f)),
                                    ((nb095AlphaDummy466 D R S_cls E),
                                      (nb095AlphaDummy468 f)),
                                    ((nb095AlphaDummy465 D R S_cls E),
                                      (nb095AlphaDummy467 f)),
                                    ((nb095AlphaDummy469 D R S_cls E),
                                      (nb095AlphaDummy470 f)),
                                    ((nb095AlphaDummy387 D R S_cls E),
                                      (nb095AlphaDummy390 f)),
                                    ((nb095AlphaDummy386 D R S_cls E),
                                      (nb095AlphaDummy389 f)),
                                    ((nb095AlphaDummy385 D R S_cls E),
                                      (nb095AlphaDummy388 f)),
                                    ((nb095AlphaDummy391 D R S_cls E),
                                      (nb095AlphaDummy392 f)),
                                    ((nb095AlphaDummy383 D R S_cls E),
                                      (nb095AlphaDummy384 f)),
                                    ((nb095AlphaDummy381 D R S_cls E),
                                      (nb095AlphaDummy382 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy515 D R S_cls E) ≠
                                      (nb095AlphaDummy519 D R S_cls E) from (by
                                      unfold nb095AlphaDummy519;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0520 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy520 f) from
                                    (by
                                      unfold nb095AlphaDummy520;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0521 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy515 D R S_cls E) ≠
                                        (nb095AlphaDummy519 D R S_cls E) from (by
                                        unfold nb095AlphaDummy519;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0520 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy520 f) from
                                      (by
                                        unfold nb095AlphaDummy520;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0521 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy519 D R S_cls E),
                                      (nb095AlphaDummy520 f)),
                                    ((nb095AlphaDummy515 D R S_cls E),
                                      (nb095AlphaDummy517 f)),
                                    ((nb095AlphaDummy516 D R S_cls E),
                                      (nb095AlphaDummy518 f)),
                                    ((nb095AlphaDummy508 D R S_cls E),
                                      (nb095AlphaDummy510 f)),
                                    ((nb095AlphaDummy507 D R S_cls E),
                                      (nb095AlphaDummy509 f)),
                                    ((nb095AlphaDummy513 D R S_cls E),
                                      (nb095AlphaDummy514 f)),
                                    ((nb095AlphaDummy511 D R S_cls E),
                                      (nb095AlphaDummy512 f)),
                                    ((nb095AlphaDummy466 D R S_cls E),
                                      (nb095AlphaDummy468 f)),
                                    ((nb095AlphaDummy465 D R S_cls E),
                                      (nb095AlphaDummy467 f)),
                                    ((nb095AlphaDummy469 D R S_cls E),
                                      (nb095AlphaDummy470 f)),
                                    ((nb095AlphaDummy387 D R S_cls E),
                                      (nb095AlphaDummy390 f)),
                                    ((nb095AlphaDummy386 D R S_cls E),
                                      (nb095AlphaDummy389 f)),
                                    ((nb095AlphaDummy385 D R S_cls E),
                                      (nb095AlphaDummy388 f)),
                                    ((nb095AlphaDummy391 D R S_cls E),
                                      (nb095AlphaDummy392 f)),
                                    ((nb095AlphaDummy383 D R S_cls E),
                                      (nb095AlphaDummy384 f)),
                                    ((nb095AlphaDummy381 D R S_cls E),
                                      (nb095AlphaDummy382 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095AlphaDummy466 D R S_cls E) ≠
                        (nb095AlphaDummy508 D R S_cls E) from (by
                        unfold nb095AlphaDummy508;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0512 D R S_cls E) 1))))
                    (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy510 f) from (by
                        unfold nb095AlphaDummy510;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0514 f) 1)))) (TAlphaVar.there
                      (show (nb095AlphaDummy466 D R S_cls E) ≠
                          (nb095AlphaDummy507 D R S_cls E) from (by
                          unfold nb095AlphaDummy507;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0512 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy509 f) from (by
                          unfold nb095AlphaDummy509;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0514 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy466 D R S_cls E) ≠
                            (nb095AlphaDummy513 D R S_cls E) from (by
                            unfold nb095AlphaDummy513;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0516 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy514 f) from (by
                            unfold nb095AlphaDummy514;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0517 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy466 D R S_cls E) ≠
                              (nb095AlphaDummy511 D R S_cls E) from (by
                              unfold nb095AlphaDummy511;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0513 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy512 f) from (by
                              unfold nb095AlphaDummy512;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0515 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy468 f))).fv ∪
                        ((Class.cv (nb095AlphaDummy467 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy508 D R S_cls E) ≠
                                (nb095AlphaDummy515 D R S_cls E) from (by
                                unfold nb095AlphaDummy515;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0518 D R S_cls E) 0))))
                            (show (nb095AlphaDummy510 f) ≠ (nb095AlphaDummy517 f) from (by
                                unfold nb095AlphaDummy517;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0519 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy508 D R S_cls E) ≠
                                  (nb095AlphaDummy516 D R S_cls E) from (by
                                  unfold nb095AlphaDummy516;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0518 D R S_cls E) 1))))
                              (show (nb095AlphaDummy510 f) ≠ (nb095AlphaDummy518 f) from
                                (by
                                  unfold nb095AlphaDummy518;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0519 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy508 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy510 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy515 D R S_cls E) ≠ (nb095AlphaDummy522 D R S_cls E) from (by
          unfold nb095AlphaDummy522;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0522 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy525 f) from (by
          unfold nb095AlphaDummy525;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0523 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy515 D R S_cls E) ≠ (nb095AlphaDummy521 D R S_cls E) from (by
          unfold nb095AlphaDummy521;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0522 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy524 f) from (by
          unfold nb095AlphaDummy524;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0523 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy515 D R S_cls E) ≠
        (nb095AlphaDummy519 D R S_cls E) from (by
          unfold nb095AlphaDummy519;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0520 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy520 f) from (by
          unfold nb095AlphaDummy520;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0521 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy523 D R S_cls E), (nb095AlphaDummy526 f)),
        ((nb095AlphaDummy522 D R S_cls E), (nb095AlphaDummy525 f)),
        ((nb095AlphaDummy521 D R S_cls E), (nb095AlphaDummy524 f)),
        ((nb095AlphaDummy519 D R S_cls E), (nb095AlphaDummy520 f)),
        ((nb095AlphaDummy515 D R S_cls E), (nb095AlphaDummy517 f)),
        ((nb095AlphaDummy516 D R S_cls E), (nb095AlphaDummy518 f)),
        ((nb095AlphaDummy508 D R S_cls E), (nb095AlphaDummy510 f)),
        ((nb095AlphaDummy507 D R S_cls E), (nb095AlphaDummy509 f)),
        ((nb095AlphaDummy513 D R S_cls E), (nb095AlphaDummy514 f)),
        ((nb095AlphaDummy511 D R S_cls E), (nb095AlphaDummy512 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy522
        D R S_cls E) ≠ (nb095AlphaDummy529 D R S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0526
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0527
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0524
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0525
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠ (nb095AlphaDummy529
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0530
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0531
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0528
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0529
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠ (nb095AlphaDummy529
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0526
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0527
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0524
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0525
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠ (nb095AlphaDummy529
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0530
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0531
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0528
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0529
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy523 D R S_cls E), (nb095AlphaDummy526 f)),
        ((nb095AlphaDummy522 D R S_cls E), (nb095AlphaDummy525 f)),
        ((nb095AlphaDummy521 D R S_cls E), (nb095AlphaDummy524 f)),
        ((nb095AlphaDummy519 D R S_cls E), (nb095AlphaDummy520 f)),
        ((nb095AlphaDummy515 D R S_cls E), (nb095AlphaDummy517 f)),
        ((nb095AlphaDummy516 D R S_cls E), (nb095AlphaDummy518 f)),
        ((nb095AlphaDummy508 D R S_cls E), (nb095AlphaDummy510 f)),
        ((nb095AlphaDummy507 D R S_cls E), (nb095AlphaDummy509 f)),
        ((nb095AlphaDummy513 D R S_cls E), (nb095AlphaDummy514 f)),
        ((nb095AlphaDummy511 D R S_cls E), (nb095AlphaDummy512 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy515 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠ (nb095AlphaDummy533
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0534
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy534 f) from (by
          unfold
            nb095AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0535
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0532
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0533
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠ (nb095AlphaDummy533
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0534
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy534 f) from (by
          unfold
            nb095AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0535
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0532
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0533
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy523
        D R S_cls E) ≠ (nb095AlphaDummy535 D R S_cls E) from (by
          unfold
            nb095AlphaDummy535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0538
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy536 f) from (by
          unfold
            nb095AlphaDummy536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0539
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0536
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0537
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy523
        D R S_cls E) ≠ (nb095AlphaDummy535 D R S_cls E) from (by
          unfold
            nb095AlphaDummy535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0538
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy536 f) from (by
          unfold
            nb095AlphaDummy536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0539
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0536
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0537
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy515 D R S_cls E) ≠
        (nb095AlphaDummy519 D R S_cls E) from (by
                                          unfold nb095AlphaDummy519;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0520 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy517 f) ≠
        (nb095AlphaDummy520 f) from (by
                                          unfold nb095AlphaDummy520;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0521 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy519 D R S_cls E),
                                        (nb095AlphaDummy520 f)),
                                      ((nb095AlphaDummy515 D R S_cls E),
                                        (nb095AlphaDummy517 f)),
                                      ((nb095AlphaDummy516 D R S_cls E),
                                        (nb095AlphaDummy518 f)),
                                      ((nb095AlphaDummy508 D R S_cls E),
                                        (nb095AlphaDummy510 f)),
                                      ((nb095AlphaDummy507 D R S_cls E),
                                        (nb095AlphaDummy509 f)),
                                      ((nb095AlphaDummy513 D R S_cls E),
                                        (nb095AlphaDummy514 f)),
                                      ((nb095AlphaDummy511 D R S_cls E),
                                        (nb095AlphaDummy512 f)),
                                      ((nb095AlphaDummy466 D R S_cls E),
                                        (nb095AlphaDummy468 f)),
                                      ((nb095AlphaDummy465 D R S_cls E),
                                        (nb095AlphaDummy467 f)),
                                      ((nb095AlphaDummy469 D R S_cls E),
                                        (nb095AlphaDummy470 f)),
                                      ((nb095AlphaDummy387 D R S_cls E),
                                        (nb095AlphaDummy390 f)),
                                      ((nb095AlphaDummy386 D R S_cls E),
                                        (nb095AlphaDummy389 f)),
                                      ((nb095AlphaDummy385 D R S_cls E),
                                        (nb095AlphaDummy388 f)),
                                      ((nb095AlphaDummy391 D R S_cls E),
                                        (nb095AlphaDummy392 f)),
                                      ((nb095AlphaDummy383 D R S_cls E),
                                        (nb095AlphaDummy384 f)),
                                      ((nb095AlphaDummy381 D R S_cls E),
                                        (nb095AlphaDummy382 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy515 D R S_cls E) ≠
                                        (nb095AlphaDummy519 D R S_cls E) from (by
                                        unfold nb095AlphaDummy519;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0520 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy520 f) from
                                      (by
                                        unfold nb095AlphaDummy520;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0521 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy515 D R S_cls E) ≠
        (nb095AlphaDummy519 D R S_cls E) from (by
                                          unfold nb095AlphaDummy519;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0520 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy517 f) ≠
        (nb095AlphaDummy520 f) from (by
                                          unfold nb095AlphaDummy520;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0521 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy519 D R S_cls E),
                                        (nb095AlphaDummy520 f)),
                                      ((nb095AlphaDummy515 D R S_cls E),
                                        (nb095AlphaDummy517 f)),
                                      ((nb095AlphaDummy516 D R S_cls E),
                                        (nb095AlphaDummy518 f)),
                                      ((nb095AlphaDummy508 D R S_cls E),
                                        (nb095AlphaDummy510 f)),
                                      ((nb095AlphaDummy507 D R S_cls E),
                                        (nb095AlphaDummy509 f)),
                                      ((nb095AlphaDummy513 D R S_cls E),
                                        (nb095AlphaDummy514 f)),
                                      ((nb095AlphaDummy511 D R S_cls E),
                                        (nb095AlphaDummy512 f)),
                                      ((nb095AlphaDummy466 D R S_cls E),
                                        (nb095AlphaDummy468 f)),
                                      ((nb095AlphaDummy465 D R S_cls E),
                                        (nb095AlphaDummy467 f)),
                                      ((nb095AlphaDummy469 D R S_cls E),
                                        (nb095AlphaDummy470 f)),
                                      ((nb095AlphaDummy387 D R S_cls E),
                                        (nb095AlphaDummy390 f)),
                                      ((nb095AlphaDummy386 D R S_cls E),
                                        (nb095AlphaDummy389 f)),
                                      ((nb095AlphaDummy385 D R S_cls E),
                                        (nb095AlphaDummy388 f)),
                                      ((nb095AlphaDummy391 D R S_cls E),
                                        (nb095AlphaDummy392 f)),
                                      ((nb095AlphaDummy383 D R S_cls E),
                                        (nb095AlphaDummy384 f)),
                                      ((nb095AlphaDummy381 D R S_cls E),
                                        (nb095AlphaDummy382 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0044`. -/
@[expose]
noncomputable def nb095SplitAlpha0044 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy541 D R S_cls E), (nb095AlphaDummy542 f)),
        ((nb095AlphaDummy539 D R S_cls E), (nb095AlphaDummy540 f)),
        ((nb095AlphaDummy508 D R S_cls E), (nb095AlphaDummy510 f)),
        ((nb095AlphaDummy507 D R S_cls E), (nb095AlphaDummy509 f)),
        ((nb095AlphaDummy537 D R S_cls E), (nb095AlphaDummy538 f)),
        ((nb095AlphaDummy511 D R S_cls E), (nb095AlphaDummy512 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy541 D R S_cls E))
          (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy541 D R S_cls E))
            (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy542 f))
          (synCphi (Class.cv (nb095AlphaDummy510 f)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy542 f))
            (synCphi (Class.cv (nb095AlphaDummy510 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy508 D R S_cls E) ≠
                      (nb095AlphaDummy515 D R S_cls E) from (by
                      unfold nb095AlphaDummy515;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0518 D R S_cls E) 0))))
                  (show (nb095AlphaDummy510 f) ≠ (nb095AlphaDummy517 f) from (by
                      unfold nb095AlphaDummy517;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0519 f) 0))))
                  (TAlphaVar.there (show (nb095AlphaDummy508 D R S_cls E) ≠
                        (nb095AlphaDummy516 D R S_cls E) from (by
                        unfold nb095AlphaDummy516;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0518 D R S_cls E) 1))))
                    (show (nb095AlphaDummy510 f) ≠ (nb095AlphaDummy518 f) from (by
                        unfold nb095AlphaDummy518;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0519 f) 1)))) (TAlphaVar.there
                      (show (nb095AlphaDummy508 D R S_cls E) ≠
                          (nb095AlphaDummy541 D R S_cls E) from (by
                          unfold nb095AlphaDummy541;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0548 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy510 f) ≠ (nb095AlphaDummy542 f) from (by
                          unfold nb095AlphaDummy542;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0549 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy508 D R S_cls E) ≠
                            (nb095AlphaDummy539 D R S_cls E) from (by
                            unfold nb095AlphaDummy539;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0546 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy510 f) ≠ (nb095AlphaDummy540 f) from (by
                            unfold nb095AlphaDummy540;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0547 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy508 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy510 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy515 D R S_cls E) ≠
                                        (nb095AlphaDummy522 D R S_cls E) from (by
                                        unfold nb095AlphaDummy522;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0522 D R S_cls E) 1)))) (show
                                      (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy525 f) from
                                      (by
                                        unfold nb095AlphaDummy525;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0523 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy515 D R S_cls E) ≠
        (nb095AlphaDummy521 D R S_cls E) from (by
                                          unfold nb095AlphaDummy521;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0522 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy517 f) ≠
        (nb095AlphaDummy524 f) from (by
                                          unfold nb095AlphaDummy524;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0523 f) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy515 D R S_cls E) ≠ (nb095AlphaDummy519 D R S_cls E) from (by
          unfold nb095AlphaDummy519;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0520 D R S_cls E)
                  0)))) (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy520 f) from (by
          unfold nb095AlphaDummy520;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0521 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [((nb095AlphaDummy523 D R S_cls E),
        (nb095AlphaDummy526 f)), ((nb095AlphaDummy522 D R S_cls E),
        (nb095AlphaDummy525 f)), ((nb095AlphaDummy521 D R S_cls E),
        (nb095AlphaDummy524 f)), ((nb095AlphaDummy519 D R S_cls E),
        (nb095AlphaDummy520 f)), ((nb095AlphaDummy515 D R S_cls E),
        (nb095AlphaDummy517 f)), ((nb095AlphaDummy516 D R S_cls E),
        (nb095AlphaDummy518 f)), ((nb095AlphaDummy541 D R S_cls E),
        (nb095AlphaDummy542 f)), ((nb095AlphaDummy539 D R S_cls E),
        (nb095AlphaDummy540 f)), ((nb095AlphaDummy508 D R S_cls E),
        (nb095AlphaDummy510 f)), ((nb095AlphaDummy507 D R S_cls E),
        (nb095AlphaDummy509 f)), ((nb095AlphaDummy537 D R S_cls E),
        (nb095AlphaDummy538 f)), ((nb095AlphaDummy511 D R S_cls E),
        (nb095AlphaDummy512 f)), ((nb095AlphaDummy466 D R S_cls E),
        (nb095AlphaDummy468 f)), ((nb095AlphaDummy465 D R S_cls E),
        (nb095AlphaDummy467 f)), ((nb095AlphaDummy469 D R S_cls E),
        (nb095AlphaDummy470 f)), ((nb095AlphaDummy387 D R S_cls E),
        (nb095AlphaDummy390 f)), ((nb095AlphaDummy386 D R S_cls E),
        (nb095AlphaDummy389 f)), ((nb095AlphaDummy385 D R S_cls E),
        (nb095AlphaDummy388 f)), ((nb095AlphaDummy391 D R S_cls E),
        (nb095AlphaDummy392 f)), ((nb095AlphaDummy383 D R S_cls E),
        (nb095AlphaDummy384 f)), ((nb095AlphaDummy381 D R S_cls E),
        (nb095AlphaDummy382 f)), ((nb095AlphaDummy001 D R S_cls E), u),
                                        ((nb095AlphaDummy002 D R S_cls E), x),
                                        ((nb095AlphaDummy000 D R S_cls E), f)]
                                      (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy522 D R S_cls E) ≠ (nb095AlphaDummy529 D R S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0526
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0527
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0524
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0525
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy529 D R S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0530
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0531
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0528
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0529
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠ (nb095AlphaDummy529 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0526
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0527
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0524
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0525
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy529 D R S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0530
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0531
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0528
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0529
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb095AlphaDummy523 D R S_cls E),
        (nb095AlphaDummy526 f)), ((nb095AlphaDummy522 D R S_cls E),
        (nb095AlphaDummy525 f)), ((nb095AlphaDummy521 D R S_cls E),
        (nb095AlphaDummy524 f)), ((nb095AlphaDummy519 D R S_cls E),
        (nb095AlphaDummy520 f)), ((nb095AlphaDummy515 D R S_cls E),
        (nb095AlphaDummy517 f)), ((nb095AlphaDummy516 D R S_cls E),
        (nb095AlphaDummy518 f)), ((nb095AlphaDummy541 D R S_cls E),
        (nb095AlphaDummy542 f)), ((nb095AlphaDummy539 D R S_cls E),
        (nb095AlphaDummy540 f)), ((nb095AlphaDummy508 D R S_cls E),
        (nb095AlphaDummy510 f)), ((nb095AlphaDummy507 D R S_cls E),
        (nb095AlphaDummy509 f)), ((nb095AlphaDummy537 D R S_cls E),
        (nb095AlphaDummy538 f)), ((nb095AlphaDummy511 D R S_cls E),
        (nb095AlphaDummy512 f)), ((nb095AlphaDummy466 D R S_cls E),
        (nb095AlphaDummy468 f)), ((nb095AlphaDummy465 D R S_cls E),
        (nb095AlphaDummy467 f)), ((nb095AlphaDummy469 D R S_cls E),
        (nb095AlphaDummy470 f)), ((nb095AlphaDummy387 D R S_cls E),
        (nb095AlphaDummy390 f)), ((nb095AlphaDummy386 D R S_cls E),
        (nb095AlphaDummy389 f)), ((nb095AlphaDummy385 D R S_cls E),
        (nb095AlphaDummy388 f)), ((nb095AlphaDummy391 D R S_cls E),
        (nb095AlphaDummy392 f)), ((nb095AlphaDummy383 D R S_cls E),
        (nb095AlphaDummy384 f)), ((nb095AlphaDummy381 D R S_cls E),
        (nb095AlphaDummy382 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb095AlphaDummy515 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy515 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy522 D R S_cls E) ≠ (nb095AlphaDummy533 D R S_cls E) from (by
          unfold
            nb095AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0534
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy534 f) from (by
          unfold
            nb095AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0535
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0532
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0533
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy533 D R S_cls E) from (by
          unfold
            nb095AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0534
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy534 f) from (by
          unfold
            nb095AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0535
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0532
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0533
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy523 D R S_cls E) ≠ (nb095AlphaDummy535 D R S_cls E) from (by
          unfold
            nb095AlphaDummy535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0538
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy536 f) from (by
          unfold
            nb095AlphaDummy536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0539
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0536
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0537
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy523 D R S_cls E) ≠ (nb095AlphaDummy535 D R S_cls E) from (by
          unfold
            nb095AlphaDummy535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0538
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy536 f) from (by
          unfold
            nb095AlphaDummy536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0539
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0536
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0537
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy515 D R S_cls E) ≠
                                (nb095AlphaDummy519 D R S_cls E) from (by
                                unfold nb095AlphaDummy519;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0520 D R S_cls E) 0))))
                            (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy520 f) from (by
                                unfold nb095AlphaDummy520;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0521 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb095AlphaDummy519 D R S_cls E), (nb095AlphaDummy520 f)),
                            ((nb095AlphaDummy515 D R S_cls E), (nb095AlphaDummy517 f)),
                            ((nb095AlphaDummy516 D R S_cls E), (nb095AlphaDummy518 f)),
                            ((nb095AlphaDummy541 D R S_cls E), (nb095AlphaDummy542 f)),
                            ((nb095AlphaDummy539 D R S_cls E), (nb095AlphaDummy540 f)),
                            ((nb095AlphaDummy508 D R S_cls E), (nb095AlphaDummy510 f)),
                            ((nb095AlphaDummy507 D R S_cls E), (nb095AlphaDummy509 f)),
                            ((nb095AlphaDummy537 D R S_cls E), (nb095AlphaDummy538 f)),
                            ((nb095AlphaDummy511 D R S_cls E), (nb095AlphaDummy512 f)),
                            ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
                            ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
                            ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
                            ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
                            ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
                            ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
                            ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
                            ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
                            ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy515 D R S_cls E) ≠
                              (nb095AlphaDummy519 D R S_cls E) from (by
                              unfold nb095AlphaDummy519;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0520 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy520 f) from (by
                              unfold nb095AlphaDummy520;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0521 f) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy515 D R S_cls E) ≠
                                (nb095AlphaDummy519 D R S_cls E) from (by
                                unfold nb095AlphaDummy519;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0520 D R S_cls E) 0))))
                            (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy520 f) from (by
                                unfold nb095AlphaDummy520;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0521 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb095AlphaDummy519 D R S_cls E), (nb095AlphaDummy520 f)),
                            ((nb095AlphaDummy515 D R S_cls E), (nb095AlphaDummy517 f)),
                            ((nb095AlphaDummy516 D R S_cls E), (nb095AlphaDummy518 f)),
                            ((nb095AlphaDummy541 D R S_cls E), (nb095AlphaDummy542 f)),
                            ((nb095AlphaDummy539 D R S_cls E), (nb095AlphaDummy540 f)),
                            ((nb095AlphaDummy508 D R S_cls E), (nb095AlphaDummy510 f)),
                            ((nb095AlphaDummy507 D R S_cls E), (nb095AlphaDummy509 f)),
                            ((nb095AlphaDummy537 D R S_cls E), (nb095AlphaDummy538 f)),
                            ((nb095AlphaDummy511 D R S_cls E), (nb095AlphaDummy512 f)),
                            ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
                            ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
                            ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
                            ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
                            ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
                            ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
                            ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
                            ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
                            ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy508 D R S_cls E) ≠
                        (nb095AlphaDummy515 D R S_cls E) from (by
                        unfold nb095AlphaDummy515;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0518 D R S_cls E) 0))))
                    (show (nb095AlphaDummy510 f) ≠ (nb095AlphaDummy517 f) from (by
                        unfold nb095AlphaDummy517;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0519 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy508 D R S_cls E) ≠
                          (nb095AlphaDummy516 D R S_cls E) from (by
                          unfold nb095AlphaDummy516;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0518 D R S_cls E)
                                  1))))
                      (show (nb095AlphaDummy510 f) ≠ (nb095AlphaDummy518 f) from (by
                          unfold nb095AlphaDummy518;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0519 f) 1))))
                      (TAlphaVar.there (show (nb095AlphaDummy508 D R S_cls E) ≠
                            (nb095AlphaDummy541 D R S_cls E) from (by
                            unfold nb095AlphaDummy541;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0548 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy510 f) ≠ (nb095AlphaDummy542 f) from (by
                            unfold nb095AlphaDummy542;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0549 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy508 D R S_cls E) ≠
                              (nb095AlphaDummy539 D R S_cls E) from (by
                              unfold nb095AlphaDummy539;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0546 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy510 f) ≠ (nb095AlphaDummy540 f) from (by
                              unfold nb095AlphaDummy540;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0547 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy508 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy510 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb095AlphaDummy515 D R S_cls E) ≠
        (nb095AlphaDummy522 D R S_cls E) from (by
                                          unfold nb095AlphaDummy522;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0522 D R S_cls E)
                                                  1)))) (show (nb095AlphaDummy517 f) ≠
        (nb095AlphaDummy525 f) from (by
                                          unfold nb095AlphaDummy525;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0523 f) 1))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy515 D R S_cls E) ≠ (nb095AlphaDummy521 D R S_cls E) from (by
          unfold nb095AlphaDummy521;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0522 D R S_cls E)
                  0)))) (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy524 f) from (by
          unfold nb095AlphaDummy524;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0523 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy515 D R S_cls E) ≠ (nb095AlphaDummy519 D R S_cls E) from (by
          unfold nb095AlphaDummy519;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0520 D R S_cls E)
                  0)))) (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy520 f) from (by
          unfold nb095AlphaDummy520;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0521 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [((nb095AlphaDummy523 D R S_cls E),
        (nb095AlphaDummy526 f)), ((nb095AlphaDummy522 D R S_cls E),
        (nb095AlphaDummy525 f)), ((nb095AlphaDummy521 D R S_cls E),
        (nb095AlphaDummy524 f)), ((nb095AlphaDummy519 D R S_cls E),
        (nb095AlphaDummy520 f)), ((nb095AlphaDummy515 D R S_cls E),
        (nb095AlphaDummy517 f)), ((nb095AlphaDummy516 D R S_cls E),
        (nb095AlphaDummy518 f)), ((nb095AlphaDummy541 D R S_cls E),
        (nb095AlphaDummy542 f)), ((nb095AlphaDummy539 D R S_cls E),
        (nb095AlphaDummy540 f)), ((nb095AlphaDummy508 D R S_cls E),
        (nb095AlphaDummy510 f)), ((nb095AlphaDummy507 D R S_cls E),
        (nb095AlphaDummy509 f)), ((nb095AlphaDummy537 D R S_cls E),
        (nb095AlphaDummy538 f)), ((nb095AlphaDummy511 D R S_cls E),
        (nb095AlphaDummy512 f)), ((nb095AlphaDummy466 D R S_cls E),
        (nb095AlphaDummy468 f)), ((nb095AlphaDummy465 D R S_cls E),
        (nb095AlphaDummy467 f)), ((nb095AlphaDummy469 D R S_cls E),
        (nb095AlphaDummy470 f)), ((nb095AlphaDummy387 D R S_cls E),
        (nb095AlphaDummy390 f)), ((nb095AlphaDummy386 D R S_cls E),
        (nb095AlphaDummy389 f)), ((nb095AlphaDummy385 D R S_cls E),
        (nb095AlphaDummy388 f)), ((nb095AlphaDummy391 D R S_cls E),
        (nb095AlphaDummy392 f)), ((nb095AlphaDummy383 D R S_cls E),
        (nb095AlphaDummy384 f)), ((nb095AlphaDummy381 D R S_cls E),
        (nb095AlphaDummy382 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy522 D R S_cls E) ≠ (nb095AlphaDummy529 D R S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0526
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0527
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0524
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0525
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠ (nb095AlphaDummy529 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0530
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0531
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0528
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0529
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠ (nb095AlphaDummy529 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0526
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0527
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0524
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0525
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠ (nb095AlphaDummy529 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0530
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0531
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0528
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0529
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy523 D R S_cls E), (nb095AlphaDummy526 f)),
        ((nb095AlphaDummy522 D R S_cls E), (nb095AlphaDummy525 f)),
        ((nb095AlphaDummy521 D R S_cls E), (nb095AlphaDummy524 f)),
        ((nb095AlphaDummy519 D R S_cls E), (nb095AlphaDummy520 f)),
        ((nb095AlphaDummy515 D R S_cls E), (nb095AlphaDummy517 f)),
        ((nb095AlphaDummy516 D R S_cls E), (nb095AlphaDummy518 f)),
        ((nb095AlphaDummy541 D R S_cls E), (nb095AlphaDummy542 f)),
        ((nb095AlphaDummy539 D R S_cls E), (nb095AlphaDummy540 f)),
        ((nb095AlphaDummy508 D R S_cls E), (nb095AlphaDummy510 f)),
        ((nb095AlphaDummy507 D R S_cls E), (nb095AlphaDummy509 f)),
        ((nb095AlphaDummy537 D R S_cls E), (nb095AlphaDummy538 f)),
        ((nb095AlphaDummy511 D R S_cls E), (nb095AlphaDummy512 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095AlphaDummy515 D R S_cls E))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515 D R S_cls
        E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy522 D R S_cls E) ≠ (nb095AlphaDummy533 D R S_cls E) from (by
          unfold
            nb095AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0534
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy534 f) from (by
          unfold
            nb095AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0535
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0532
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0533
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠ (nb095AlphaDummy533 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0534
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy534 f) from (by
          unfold
            nb095AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0535
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0532
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0533
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy523 D R S_cls E) ≠ (nb095AlphaDummy535 D R S_cls E) from (by
          unfold
            nb095AlphaDummy535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0538
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy536 f) from (by
          unfold
            nb095AlphaDummy536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0539
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0536
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0537
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy523 D R S_cls E) ≠ (nb095AlphaDummy535 D R S_cls E) from (by
          unfold
            nb095AlphaDummy535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0538
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy536 f) from (by
          unfold
            nb095AlphaDummy536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0539
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0536
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0537
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095AlphaDummy515 D R S_cls E) ≠
                                  (nb095AlphaDummy519 D R S_cls E) from (by
                                  unfold nb095AlphaDummy519;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0520 D R S_cls E) 0))))
                              (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy520 f) from
                                (by
                                  unfold nb095AlphaDummy520;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0521 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb095AlphaDummy519 D R S_cls E), (nb095AlphaDummy520 f)),
                              ((nb095AlphaDummy515 D R S_cls E), (nb095AlphaDummy517 f)),
                              ((nb095AlphaDummy516 D R S_cls E), (nb095AlphaDummy518 f)),
                              ((nb095AlphaDummy541 D R S_cls E), (nb095AlphaDummy542 f)),
                              ((nb095AlphaDummy539 D R S_cls E), (nb095AlphaDummy540 f)),
                              ((nb095AlphaDummy508 D R S_cls E), (nb095AlphaDummy510 f)),
                              ((nb095AlphaDummy507 D R S_cls E), (nb095AlphaDummy509 f)),
                              ((nb095AlphaDummy537 D R S_cls E), (nb095AlphaDummy538 f)),
                              ((nb095AlphaDummy511 D R S_cls E), (nb095AlphaDummy512 f)),
                              ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
                              ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
                              ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
                              ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
                              ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
                              ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
                              ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
                              ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
                              ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
                              ((nb095AlphaDummy001 D R S_cls E), u),
                              ((nb095AlphaDummy002 D R S_cls E), x),
                              ((nb095AlphaDummy000 D R S_cls E), f)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy515 D R S_cls E) ≠
                                (nb095AlphaDummy519 D R S_cls E) from (by
                                unfold nb095AlphaDummy519;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0520 D R S_cls E) 0))))
                            (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy520 f) from (by
                                unfold nb095AlphaDummy520;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0521 f) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095AlphaDummy515 D R S_cls E) ≠
                                  (nb095AlphaDummy519 D R S_cls E) from (by
                                  unfold nb095AlphaDummy519;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0520 D R S_cls E) 0))))
                              (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy520 f) from
                                (by
                                  unfold nb095AlphaDummy520;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0521 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb095AlphaDummy519 D R S_cls E), (nb095AlphaDummy520 f)),
                              ((nb095AlphaDummy515 D R S_cls E), (nb095AlphaDummy517 f)),
                              ((nb095AlphaDummy516 D R S_cls E), (nb095AlphaDummy518 f)),
                              ((nb095AlphaDummy541 D R S_cls E), (nb095AlphaDummy542 f)),
                              ((nb095AlphaDummy539 D R S_cls E), (nb095AlphaDummy540 f)),
                              ((nb095AlphaDummy508 D R S_cls E), (nb095AlphaDummy510 f)),
                              ((nb095AlphaDummy507 D R S_cls E), (nb095AlphaDummy509 f)),
                              ((nb095AlphaDummy537 D R S_cls E), (nb095AlphaDummy538 f)),
                              ((nb095AlphaDummy511 D R S_cls E), (nb095AlphaDummy512 f)),
                              ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
                              ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
                              ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
                              ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
                              ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
                              ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
                              ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
                              ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
                              ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
                              ((nb095AlphaDummy001 D R S_cls E), u),
                              ((nb095AlphaDummy002 D R S_cls E), x),
                              ((nb095AlphaDummy000 D R S_cls E), f)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0045`. -/
@[expose]
noncomputable def nb095SplitAlpha0045 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy103 D R S_cls E), (nb095AlphaDummy104 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy103 D R S_cls E))
          (Class.cab (nb095AlphaDummy097 D R S_cls E)
            (synWrex (nb095AlphaDummy098 D R S_cls E)
              (Class.cv (nb095AlphaDummy091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy103 D R S_cls E))
            (Class.cab (nb095AlphaDummy097 D R S_cls E)
              (synWrex (nb095AlphaDummy098 D R S_cls E)
                (Class.cv (nb095AlphaDummy091 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy104 f))
          (Class.cab (nb095AlphaDummy099 f)
            (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy093 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                (synCphi (Class.cv (nb095AlphaDummy100 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy104 f))
            (Class.cab (nb095AlphaDummy099 f)
              (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy093 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                  (synCphi (Class.cv (nb095AlphaDummy100 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                      (nb095AlphaDummy098 D R S_cls E) from (by
                      unfold nb095AlphaDummy098;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 1))))
                  (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy100 f) from (by
                      unfold nb095AlphaDummy100;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0086 f) 1))))
                  (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                        (nb095AlphaDummy097 D R S_cls E) from (by
                        unfold nb095AlphaDummy097;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 0))))
                    (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy099 f) from (by
                        unfold nb095AlphaDummy099;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0086 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy091 D R S_cls E) ≠
                          (nb095AlphaDummy103 D R S_cls E) from (by
                          unfold nb095AlphaDummy103;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0088 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy104 f) from (by
                          unfold nb095AlphaDummy104;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0089 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                            (nb095AlphaDummy101 D R S_cls E) from (by
                            unfold nb095AlphaDummy101;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0085 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy102 f) from (by
                            unfold nb095AlphaDummy102;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0087 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪
                      ((Class.cv (nb095AlphaDummy094 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                              (nb095AlphaDummy105 D R S_cls E) from (by
                              unfold nb095AlphaDummy105;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0090 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy107 f) from (by
                              unfold nb095AlphaDummy107;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0091 f) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                                (nb095AlphaDummy106 D R S_cls E) from (by
                                unfold nb095AlphaDummy106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0090 D R S_cls E) 1))))
                            (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy108 f) from (by
                                unfold nb095AlphaDummy108;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0091 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy098 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy100 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy105 D R S_cls E) ≠
        (nb095AlphaDummy112 D R S_cls E) from (by
          unfold nb095AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy115 f) from (by
          unfold nb095AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy111 D R S_cls E) from (by
          unfold nb095AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy114 f) from (by
          unfold nb095AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy109 D R S_cls E) from (by
          unfold nb095AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0092 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from (by
          unfold nb095AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy103 D R S_cls E), (nb095AlphaDummy104 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy112
        D R S_cls E) ≠ (nb095AlphaDummy119 D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy103 D R S_cls E), (nb095AlphaDummy104 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113
        D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113
        D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy105 D R S_cls E) ≠
                                        (nb095AlphaDummy109 D R S_cls E) from (by
                                        unfold nb095AlphaDummy109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                      (by
                                        unfold nb095AlphaDummy110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy109 D R S_cls E),
                                      (nb095AlphaDummy110 f)),
                                    ((nb095AlphaDummy105 D R S_cls E),
                                      (nb095AlphaDummy107 f)),
                                    ((nb095AlphaDummy106 D R S_cls E),
                                      (nb095AlphaDummy108 f)),
                                    ((nb095AlphaDummy098 D R S_cls E),
                                      (nb095AlphaDummy100 f)),
                                    ((nb095AlphaDummy097 D R S_cls E),
                                      (nb095AlphaDummy099 f)),
                                    ((nb095AlphaDummy103 D R S_cls E),
                                      (nb095AlphaDummy104 f)),
                                    ((nb095AlphaDummy101 D R S_cls E),
                                      (nb095AlphaDummy102 f)),
                                    ((nb095AlphaDummy092 D R S_cls E),
                                      (nb095AlphaDummy094 f)),
                                    ((nb095AlphaDummy091 D R S_cls E),
                                      (nb095AlphaDummy093 f)),
                                    ((nb095AlphaDummy095 D R S_cls E),
                                      (nb095AlphaDummy096 f)),
                                    ((nb095AlphaDummy466 D R S_cls E),
                                      (nb095AlphaDummy468 f)),
                                    ((nb095AlphaDummy465 D R S_cls E),
                                      (nb095AlphaDummy467 f)),
                                    ((nb095AlphaDummy469 D R S_cls E),
                                      (nb095AlphaDummy470 f)),
                                    ((nb095AlphaDummy387 D R S_cls E),
                                      (nb095AlphaDummy390 f)),
                                    ((nb095AlphaDummy386 D R S_cls E),
                                      (nb095AlphaDummy389 f)),
                                    ((nb095AlphaDummy385 D R S_cls E),
                                      (nb095AlphaDummy388 f)),
                                    ((nb095AlphaDummy391 D R S_cls E),
                                      (nb095AlphaDummy392 f)),
                                    ((nb095AlphaDummy383 D R S_cls E),
                                      (nb095AlphaDummy384 f)),
                                    ((nb095AlphaDummy381 D R S_cls E),
                                      (nb095AlphaDummy382 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy105 D R S_cls E) ≠
                                      (nb095AlphaDummy109 D R S_cls E) from (by
                                      unfold nb095AlphaDummy109;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                    (by
                                      unfold nb095AlphaDummy110;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0093 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy105 D R S_cls E) ≠
                                        (nb095AlphaDummy109 D R S_cls E) from (by
                                        unfold nb095AlphaDummy109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                      (by
                                        unfold nb095AlphaDummy110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy109 D R S_cls E),
                                      (nb095AlphaDummy110 f)),
                                    ((nb095AlphaDummy105 D R S_cls E),
                                      (nb095AlphaDummy107 f)),
                                    ((nb095AlphaDummy106 D R S_cls E),
                                      (nb095AlphaDummy108 f)),
                                    ((nb095AlphaDummy098 D R S_cls E),
                                      (nb095AlphaDummy100 f)),
                                    ((nb095AlphaDummy097 D R S_cls E),
                                      (nb095AlphaDummy099 f)),
                                    ((nb095AlphaDummy103 D R S_cls E),
                                      (nb095AlphaDummy104 f)),
                                    ((nb095AlphaDummy101 D R S_cls E),
                                      (nb095AlphaDummy102 f)),
                                    ((nb095AlphaDummy092 D R S_cls E),
                                      (nb095AlphaDummy094 f)),
                                    ((nb095AlphaDummy091 D R S_cls E),
                                      (nb095AlphaDummy093 f)),
                                    ((nb095AlphaDummy095 D R S_cls E),
                                      (nb095AlphaDummy096 f)),
                                    ((nb095AlphaDummy466 D R S_cls E),
                                      (nb095AlphaDummy468 f)),
                                    ((nb095AlphaDummy465 D R S_cls E),
                                      (nb095AlphaDummy467 f)),
                                    ((nb095AlphaDummy469 D R S_cls E),
                                      (nb095AlphaDummy470 f)),
                                    ((nb095AlphaDummy387 D R S_cls E),
                                      (nb095AlphaDummy390 f)),
                                    ((nb095AlphaDummy386 D R S_cls E),
                                      (nb095AlphaDummy389 f)),
                                    ((nb095AlphaDummy385 D R S_cls E),
                                      (nb095AlphaDummy388 f)),
                                    ((nb095AlphaDummy391 D R S_cls E),
                                      (nb095AlphaDummy392 f)),
                                    ((nb095AlphaDummy383 D R S_cls E),
                                      (nb095AlphaDummy384 f)),
                                    ((nb095AlphaDummy381 D R S_cls E),
                                      (nb095AlphaDummy382 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                        (nb095AlphaDummy098 D R S_cls E) from (by
                        unfold nb095AlphaDummy098;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 1))))
                    (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy100 f) from (by
                        unfold nb095AlphaDummy100;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0086 f) 1)))) (TAlphaVar.there
                      (show (nb095AlphaDummy091 D R S_cls E) ≠
                          (nb095AlphaDummy097 D R S_cls E) from (by
                          unfold nb095AlphaDummy097;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy099 f) from (by
                          unfold nb095AlphaDummy099;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0086 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                            (nb095AlphaDummy103 D R S_cls E) from (by
                            unfold nb095AlphaDummy103;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0088 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy104 f) from (by
                            unfold nb095AlphaDummy104;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0089 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                              (nb095AlphaDummy101 D R S_cls E) from (by
                              unfold nb095AlphaDummy101;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0085 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy102 f) from (by
                              unfold nb095AlphaDummy102;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0087 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv) (by decide))
                            (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪
                        ((Class.cv (nb095AlphaDummy094 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy098 D R S_cls E) ≠
                                (nb095AlphaDummy105 D R S_cls E) from (by
                                unfold nb095AlphaDummy105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0090 D R S_cls E) 0))))
                            (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy107 f) from (by
                                unfold nb095AlphaDummy107;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0091 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                                  (nb095AlphaDummy106 D R S_cls E) from (by
                                  unfold nb095AlphaDummy106;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0090 D R S_cls E) 1))))
                              (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy108 f) from
                                (by
                                  unfold nb095AlphaDummy108;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0091 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy098 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy100 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy112 D R S_cls E) from (by
          unfold nb095AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy115 f) from (by
          unfold nb095AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy111 D R S_cls E) from (by
          unfold nb095AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy114 f) from (by
          unfold nb095AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy105 D R S_cls E) ≠
        (nb095AlphaDummy109 D R S_cls E) from (by
          unfold nb095AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0092 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from (by
          unfold nb095AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy103 D R S_cls E), (nb095AlphaDummy104 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy112
        D R S_cls E) ≠ (nb095AlphaDummy119 D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy103 D R S_cls E), (nb095AlphaDummy104 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113
        D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113
        D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy105 D R S_cls E) ≠
        (nb095AlphaDummy109 D R S_cls E) from (by
                                          unfold nb095AlphaDummy109;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0092 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy107 f) ≠
        (nb095AlphaDummy110 f) from (by
                                          unfold nb095AlphaDummy110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0093 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy109 D R S_cls E),
                                        (nb095AlphaDummy110 f)),
                                      ((nb095AlphaDummy105 D R S_cls E),
                                        (nb095AlphaDummy107 f)),
                                      ((nb095AlphaDummy106 D R S_cls E),
                                        (nb095AlphaDummy108 f)),
                                      ((nb095AlphaDummy098 D R S_cls E),
                                        (nb095AlphaDummy100 f)),
                                      ((nb095AlphaDummy097 D R S_cls E),
                                        (nb095AlphaDummy099 f)),
                                      ((nb095AlphaDummy103 D R S_cls E),
                                        (nb095AlphaDummy104 f)),
                                      ((nb095AlphaDummy101 D R S_cls E),
                                        (nb095AlphaDummy102 f)),
                                      ((nb095AlphaDummy092 D R S_cls E),
                                        (nb095AlphaDummy094 f)),
                                      ((nb095AlphaDummy091 D R S_cls E),
                                        (nb095AlphaDummy093 f)),
                                      ((nb095AlphaDummy095 D R S_cls E),
                                        (nb095AlphaDummy096 f)),
                                      ((nb095AlphaDummy466 D R S_cls E),
                                        (nb095AlphaDummy468 f)),
                                      ((nb095AlphaDummy465 D R S_cls E),
                                        (nb095AlphaDummy467 f)),
                                      ((nb095AlphaDummy469 D R S_cls E),
                                        (nb095AlphaDummy470 f)),
                                      ((nb095AlphaDummy387 D R S_cls E),
                                        (nb095AlphaDummy390 f)),
                                      ((nb095AlphaDummy386 D R S_cls E),
                                        (nb095AlphaDummy389 f)),
                                      ((nb095AlphaDummy385 D R S_cls E),
                                        (nb095AlphaDummy388 f)),
                                      ((nb095AlphaDummy391 D R S_cls E),
                                        (nb095AlphaDummy392 f)),
                                      ((nb095AlphaDummy383 D R S_cls E),
                                        (nb095AlphaDummy384 f)),
                                      ((nb095AlphaDummy381 D R S_cls E),
                                        (nb095AlphaDummy382 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy105 D R S_cls E) ≠
                                        (nb095AlphaDummy109 D R S_cls E) from (by
                                        unfold nb095AlphaDummy109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                      (by
                                        unfold nb095AlphaDummy110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy105 D R S_cls E) ≠
        (nb095AlphaDummy109 D R S_cls E) from (by
                                          unfold nb095AlphaDummy109;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0092 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy107 f) ≠
        (nb095AlphaDummy110 f) from (by
                                          unfold nb095AlphaDummy110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0093 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy109 D R S_cls E),
                                        (nb095AlphaDummy110 f)),
                                      ((nb095AlphaDummy105 D R S_cls E),
                                        (nb095AlphaDummy107 f)),
                                      ((nb095AlphaDummy106 D R S_cls E),
                                        (nb095AlphaDummy108 f)),
                                      ((nb095AlphaDummy098 D R S_cls E),
                                        (nb095AlphaDummy100 f)),
                                      ((nb095AlphaDummy097 D R S_cls E),
                                        (nb095AlphaDummy099 f)),
                                      ((nb095AlphaDummy103 D R S_cls E),
                                        (nb095AlphaDummy104 f)),
                                      ((nb095AlphaDummy101 D R S_cls E),
                                        (nb095AlphaDummy102 f)),
                                      ((nb095AlphaDummy092 D R S_cls E),
                                        (nb095AlphaDummy094 f)),
                                      ((nb095AlphaDummy091 D R S_cls E),
                                        (nb095AlphaDummy093 f)),
                                      ((nb095AlphaDummy095 D R S_cls E),
                                        (nb095AlphaDummy096 f)),
                                      ((nb095AlphaDummy466 D R S_cls E),
                                        (nb095AlphaDummy468 f)),
                                      ((nb095AlphaDummy465 D R S_cls E),
                                        (nb095AlphaDummy467 f)),
                                      ((nb095AlphaDummy469 D R S_cls E),
                                        (nb095AlphaDummy470 f)),
                                      ((nb095AlphaDummy387 D R S_cls E),
                                        (nb095AlphaDummy390 f)),
                                      ((nb095AlphaDummy386 D R S_cls E),
                                        (nb095AlphaDummy389 f)),
                                      ((nb095AlphaDummy385 D R S_cls E),
                                        (nb095AlphaDummy388 f)),
                                      ((nb095AlphaDummy391 D R S_cls E),
                                        (nb095AlphaDummy392 f)),
                                      ((nb095AlphaDummy383 D R S_cls E),
                                        (nb095AlphaDummy384 f)),
                                      ((nb095AlphaDummy381 D R S_cls E),
                                        (nb095AlphaDummy382 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
