/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block017

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part054`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0031`. -/
@[expose]
noncomputable def nb090SplitAlpha0031 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy343 A), (nb090AlphaDummy344 h)),
        ((nb090AlphaDummy341 A), (nb090AlphaDummy342 h)),
        ((nb090AlphaDummy334 A), (nb090AlphaDummy336 h)),
        ((nb090AlphaDummy333 A), (nb090AlphaDummy335 h)),
        ((nb090AlphaDummy331 A), (nb090AlphaDummy332 v h)),
        ((nb090AlphaDummy329 A), (nb090AlphaDummy330 v h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy343 A))
          (Class.cab (nb090AlphaDummy337 A)
            (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy334 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                (synCphi (Class.cv (nb090AlphaDummy338 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy343 A))
            (Class.cab (nb090AlphaDummy337 A)
              (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy334 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                  (synCphi (Class.cv (nb090AlphaDummy338 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy344 h))
          (Class.cab (nb090AlphaDummy339 h)
            (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy336 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                (synCphi (Class.cv (nb090AlphaDummy340 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy344 h))
            (Class.cab (nb090AlphaDummy339 h)
              (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy336 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                  (synCphi (Class.cv (nb090AlphaDummy340 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy334 A) ≠ (nb090AlphaDummy338 A) from (by
                      unfold nb090AlphaDummy338;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0338 A) 1))))
                  (show (nb090AlphaDummy336 h) ≠ (nb090AlphaDummy340 h) from (by
                      unfold nb090AlphaDummy340;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0340 h) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy334 A) ≠ (nb090AlphaDummy337 A) from (by
                        unfold nb090AlphaDummy337;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0338 A) 0))))
                    (show (nb090AlphaDummy336 h) ≠ (nb090AlphaDummy339 h) from (by
                        unfold nb090AlphaDummy339;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0340 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy334 A) ≠ (nb090AlphaDummy343 A) from (by
                          unfold nb090AlphaDummy343;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0342 A) 0))))
                      (show (nb090AlphaDummy336 h) ≠ (nb090AlphaDummy344 h) from (by
                          unfold nb090AlphaDummy344;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0343 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy334 A) ≠ (nb090AlphaDummy341 A) from (by
                            unfold nb090AlphaDummy341;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0339 A) 0))))
                        (show (nb090AlphaDummy336 h) ≠ (nb090AlphaDummy342 h) from (by
                            unfold nb090AlphaDummy342;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0341 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy334 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy333 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090AlphaDummy336 h))).fv ∪
                      ((Class.cv (nb090AlphaDummy335 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy338 A) ≠ (nb090AlphaDummy345 A) from (by
                              unfold nb090AlphaDummy345;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0344 A) 0))))
                          (show (nb090AlphaDummy340 h) ≠ (nb090AlphaDummy347 h) from (by
                              unfold nb090AlphaDummy347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0345 h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy338 A) ≠ (nb090AlphaDummy346 A) from (by
                                unfold nb090AlphaDummy346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0344 A) 1))))
                            (show (nb090AlphaDummy340 h) ≠ (nb090AlphaDummy348 h) from (by
                                unfold nb090AlphaDummy348;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0345 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy338 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy340 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy352 A) from (by
          unfold nb090AlphaDummy352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0348 A) 1)))) (show (nb090AlphaDummy347 h) ≠
        (nb090AlphaDummy355 h) from (by
          unfold nb090AlphaDummy355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy351 A) from (by
          unfold nb090AlphaDummy351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0348 A) 0)))) (show (nb090AlphaDummy347 h) ≠
        (nb090AlphaDummy354 h) from (by
          unfold nb090AlphaDummy354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy349 A) from (by
          unfold nb090AlphaDummy349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346 A)
                  0)))) (show (nb090AlphaDummy347 h) ≠ (nb090AlphaDummy350 h) from (by
          unfold nb090AlphaDummy350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy353 A), (nb090AlphaDummy356 h)), ((nb090AlphaDummy352 A),
        (nb090AlphaDummy355 h)), ((nb090AlphaDummy351 A), (nb090AlphaDummy354 h)),
        ((nb090AlphaDummy349 A), (nb090AlphaDummy350 h)), ((nb090AlphaDummy345 A),
        (nb090AlphaDummy347 h)), ((nb090AlphaDummy346 A), (nb090AlphaDummy348 h)),
        ((nb090AlphaDummy338 A), (nb090AlphaDummy340 h)), ((nb090AlphaDummy337 A),
        (nb090AlphaDummy339 h)), ((nb090AlphaDummy343 A), (nb090AlphaDummy344 h)),
        ((nb090AlphaDummy341 A), (nb090AlphaDummy342 h)), ((nb090AlphaDummy334 A),
        (nb090AlphaDummy336 h)), ((nb090AlphaDummy333 A), (nb090AlphaDummy335 h)),
        ((nb090AlphaDummy331 A), (nb090AlphaDummy332 v h)), ((nb090AlphaDummy329 A),
        (nb090AlphaDummy330 v h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠ (nb090AlphaDummy359 A) from (by
          unfold
            nb090AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0352
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy360 h) from (by
          unfold
            nb090AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0353
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠
        (nb090AlphaDummy357 A) from (by
          unfold
            nb090AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0350
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy358 h) from (by
          unfold
            nb090AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0351
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy345
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠ (nb090AlphaDummy359 A) from (by
          unfold
            nb090AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0356
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy360 h) from (by
          unfold
            nb090AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0357
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠
        (nb090AlphaDummy357 A) from (by
          unfold
            nb090AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0354
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy358 h) from (by
          unfold
            nb090AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0355
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠ (nb090AlphaDummy359 A) from (by
          unfold
            nb090AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0352
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy360 h) from (by
          unfold
            nb090AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0353
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠
        (nb090AlphaDummy357 A) from (by
          unfold
            nb090AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0350
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy358 h) from (by
          unfold
            nb090AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0351
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy345
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠ (nb090AlphaDummy359 A) from (by
          unfold
            nb090AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0356
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy360 h) from (by
          unfold
            nb090AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0357
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠
        (nb090AlphaDummy357 A) from (by
          unfold
            nb090AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0354
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy358 h) from (by
          unfold
            nb090AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0355
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy353 A), (nb090AlphaDummy356 h)), ((nb090AlphaDummy352 A),
        (nb090AlphaDummy355 h)), ((nb090AlphaDummy351 A), (nb090AlphaDummy354 h)),
        ((nb090AlphaDummy349 A), (nb090AlphaDummy350 h)), ((nb090AlphaDummy345 A),
        (nb090AlphaDummy347 h)), ((nb090AlphaDummy346 A), (nb090AlphaDummy348 h)),
        ((nb090AlphaDummy338 A), (nb090AlphaDummy340 h)), ((nb090AlphaDummy337 A),
        (nb090AlphaDummy339 h)), ((nb090AlphaDummy343 A), (nb090AlphaDummy344 h)),
        ((nb090AlphaDummy341 A), (nb090AlphaDummy342 h)), ((nb090AlphaDummy334 A),
        (nb090AlphaDummy336 h)), ((nb090AlphaDummy333 A), (nb090AlphaDummy335 h)),
        ((nb090AlphaDummy331 A), (nb090AlphaDummy332 v h)), ((nb090AlphaDummy329 A),
        (nb090AlphaDummy330 v h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy345 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy345 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy347 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy352
        A) ≠ (nb090AlphaDummy363 A) from (by
          unfold
            nb090AlphaDummy363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0360
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy364 h) from (by
          unfold
            nb090AlphaDummy364;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0361
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠
        (nb090AlphaDummy361 A) from (by
          unfold
            nb090AlphaDummy361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0358
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy362 h) from (by
          unfold
            nb090AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0359
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy345
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠ (nb090AlphaDummy363 A) from (by
          unfold
            nb090AlphaDummy363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0360
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy364 h) from (by
          unfold
            nb090AlphaDummy364;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0361
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠
        (nb090AlphaDummy361 A) from (by
          unfold
            nb090AlphaDummy361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0358
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy362 h) from (by
          unfold
            nb090AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0359
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy345
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy353
        A) ≠ (nb090AlphaDummy365 A) from (by
          unfold
            nb090AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0364
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy366 h) from (by
          unfold
            nb090AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0365
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠
        (nb090AlphaDummy361 A) from (by
          unfold
            nb090AlphaDummy361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0362
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy362 h) from (by
          unfold
            nb090AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0363
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy353
        A) ≠ (nb090AlphaDummy365 A) from (by
          unfold
            nb090AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0364
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy366 h) from (by
          unfold
            nb090AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0365
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠
        (nb090AlphaDummy361 A) from (by
          unfold
            nb090AlphaDummy361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0362
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy362 h) from (by
          unfold
            nb090AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0363
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy349 A) from
                                      (by
                                        unfold nb090AlphaDummy349;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0346 A)
                                                0)))) (show (nb090AlphaDummy347 h) ≠
                                        (nb090AlphaDummy350 h) from (by
                                        unfold nb090AlphaDummy350;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0347 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy349 A), (nb090AlphaDummy350 h)),
                                    ((nb090AlphaDummy345 A), (nb090AlphaDummy347 h)),
                                    ((nb090AlphaDummy346 A), (nb090AlphaDummy348 h)),
                                    ((nb090AlphaDummy338 A), (nb090AlphaDummy340 h)),
                                    ((nb090AlphaDummy337 A), (nb090AlphaDummy339 h)),
                                    ((nb090AlphaDummy343 A), (nb090AlphaDummy344 h)),
                                    ((nb090AlphaDummy341 A), (nb090AlphaDummy342 h)),
                                    ((nb090AlphaDummy334 A), (nb090AlphaDummy336 h)),
                                    ((nb090AlphaDummy333 A), (nb090AlphaDummy335 h)),
                                    ((nb090AlphaDummy331 A), (nb090AlphaDummy332 v h)),
                                    ((nb090AlphaDummy329 A), (nb090AlphaDummy330 v h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy349 A) from
                                    (by
                                      unfold nb090AlphaDummy349;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0346 A)
                                              0)))) (show
                                    (nb090AlphaDummy347 h) ≠ (nb090AlphaDummy350 h) from
                                    (by
                                      unfold nb090AlphaDummy350;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0347 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy349 A) from
                                      (by
                                        unfold nb090AlphaDummy349;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0346 A)
                                                0)))) (show (nb090AlphaDummy347 h) ≠
                                        (nb090AlphaDummy350 h) from (by
                                        unfold nb090AlphaDummy350;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0347 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy349 A), (nb090AlphaDummy350 h)),
                                    ((nb090AlphaDummy345 A), (nb090AlphaDummy347 h)),
                                    ((nb090AlphaDummy346 A), (nb090AlphaDummy348 h)),
                                    ((nb090AlphaDummy338 A), (nb090AlphaDummy340 h)),
                                    ((nb090AlphaDummy337 A), (nb090AlphaDummy339 h)),
                                    ((nb090AlphaDummy343 A), (nb090AlphaDummy344 h)),
                                    ((nb090AlphaDummy341 A), (nb090AlphaDummy342 h)),
                                    ((nb090AlphaDummy334 A), (nb090AlphaDummy336 h)),
                                    ((nb090AlphaDummy333 A), (nb090AlphaDummy335 h)),
                                    ((nb090AlphaDummy331 A), (nb090AlphaDummy332 v h)),
                                    ((nb090AlphaDummy329 A), (nb090AlphaDummy330 v h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090AlphaDummy334 A) ≠ (nb090AlphaDummy338 A) from (by
                        unfold nb090AlphaDummy338;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0338 A) 1))))
                    (show (nb090AlphaDummy336 h) ≠ (nb090AlphaDummy340 h) from (by
                        unfold nb090AlphaDummy340;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0340 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy334 A) ≠ (nb090AlphaDummy337 A) from (by
                          unfold nb090AlphaDummy337;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0338 A) 0))))
                      (show (nb090AlphaDummy336 h) ≠ (nb090AlphaDummy339 h) from (by
                          unfold nb090AlphaDummy339;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0340 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy334 A) ≠ (nb090AlphaDummy343 A) from (by
                            unfold nb090AlphaDummy343;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0342 A) 0))))
                        (show (nb090AlphaDummy336 h) ≠ (nb090AlphaDummy344 h) from (by
                            unfold nb090AlphaDummy344;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0343 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy334 A) ≠ (nb090AlphaDummy341 A) from (by
                              unfold nb090AlphaDummy341;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0339 A) 0))))
                          (show (nb090AlphaDummy336 h) ≠ (nb090AlphaDummy342 h) from (by
                              unfold nb090AlphaDummy342;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0341 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy334 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy333 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy336 h))).fv ∪
                        ((Class.cv (nb090AlphaDummy335 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy338 A) ≠ (nb090AlphaDummy345 A) from (by
                                unfold nb090AlphaDummy345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0344 A) 0))))
                            (show (nb090AlphaDummy340 h) ≠ (nb090AlphaDummy347 h) from (by
                                unfold nb090AlphaDummy347;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0345 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy338 A) ≠ (nb090AlphaDummy346 A) from
                                (by
                                  unfold nb090AlphaDummy346;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0344 A) 1))))
                              (show (nb090AlphaDummy340 h) ≠ (nb090AlphaDummy348 h) from
                                (by
                                  unfold nb090AlphaDummy348;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0345 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy338 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy340 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy352 A) from (by
          unfold nb090AlphaDummy352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0348 A) 1)))) (show (nb090AlphaDummy347 h) ≠
        (nb090AlphaDummy355 h) from (by
          unfold nb090AlphaDummy355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy351 A) from (by
          unfold nb090AlphaDummy351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0348 A)
                  0)))) (show (nb090AlphaDummy347 h) ≠ (nb090AlphaDummy354 h) from (by
          unfold nb090AlphaDummy354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy345 A) ≠
        (nb090AlphaDummy349 A) from (by
          unfold nb090AlphaDummy349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346 A)
                  0)))) (show (nb090AlphaDummy347 h) ≠ (nb090AlphaDummy350 h) from (by
          unfold nb090AlphaDummy350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy353 A), (nb090AlphaDummy356 h)), ((nb090AlphaDummy352 A),
        (nb090AlphaDummy355 h)), ((nb090AlphaDummy351 A), (nb090AlphaDummy354 h)),
        ((nb090AlphaDummy349 A), (nb090AlphaDummy350 h)), ((nb090AlphaDummy345 A),
        (nb090AlphaDummy347 h)), ((nb090AlphaDummy346 A), (nb090AlphaDummy348 h)),
        ((nb090AlphaDummy338 A), (nb090AlphaDummy340 h)), ((nb090AlphaDummy337 A),
        (nb090AlphaDummy339 h)), ((nb090AlphaDummy343 A), (nb090AlphaDummy344 h)),
        ((nb090AlphaDummy341 A), (nb090AlphaDummy342 h)), ((nb090AlphaDummy334 A),
        (nb090AlphaDummy336 h)), ((nb090AlphaDummy333 A), (nb090AlphaDummy335 h)),
        ((nb090AlphaDummy331 A), (nb090AlphaDummy332 v h)), ((nb090AlphaDummy329 A),
        (nb090AlphaDummy330 v h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠ (nb090AlphaDummy359 A) from (by
          unfold
            nb090AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0352
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy360 h) from (by
          unfold
            nb090AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0353
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠
        (nb090AlphaDummy357 A) from (by
          unfold
            nb090AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0350
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy358 h) from (by
          unfold
            nb090AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0351
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy345
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠ (nb090AlphaDummy359 A) from (by
          unfold
            nb090AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0356
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy360 h) from (by
          unfold
            nb090AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0357
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠
        (nb090AlphaDummy357 A) from (by
          unfold
            nb090AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0354
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy358 h) from (by
          unfold
            nb090AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0355
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠ (nb090AlphaDummy359 A) from (by
          unfold
            nb090AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0352
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy360 h) from (by
          unfold
            nb090AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0353
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠
        (nb090AlphaDummy357 A) from (by
          unfold
            nb090AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0350
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy358 h) from (by
          unfold
            nb090AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0351
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy345
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠ (nb090AlphaDummy359 A) from (by
          unfold
            nb090AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0356
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy360 h) from (by
          unfold
            nb090AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0357
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠
        (nb090AlphaDummy357 A) from (by
          unfold
            nb090AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0354
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy358 h) from (by
          unfold
            nb090AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0355
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy353 A), (nb090AlphaDummy356 h)), ((nb090AlphaDummy352 A),
        (nb090AlphaDummy355 h)), ((nb090AlphaDummy351 A), (nb090AlphaDummy354 h)),
        ((nb090AlphaDummy349 A), (nb090AlphaDummy350 h)), ((nb090AlphaDummy345 A),
        (nb090AlphaDummy347 h)), ((nb090AlphaDummy346 A), (nb090AlphaDummy348 h)),
        ((nb090AlphaDummy338 A), (nb090AlphaDummy340 h)), ((nb090AlphaDummy337 A),
        (nb090AlphaDummy339 h)), ((nb090AlphaDummy343 A), (nb090AlphaDummy344 h)),
        ((nb090AlphaDummy341 A), (nb090AlphaDummy342 h)), ((nb090AlphaDummy334 A),
        (nb090AlphaDummy336 h)), ((nb090AlphaDummy333 A), (nb090AlphaDummy335 h)),
        ((nb090AlphaDummy331 A), (nb090AlphaDummy332 v h)), ((nb090AlphaDummy329 A),
        (nb090AlphaDummy330 v h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy345 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy347
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy345 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy352
        A) ≠ (nb090AlphaDummy363 A) from (by
          unfold
            nb090AlphaDummy363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0360
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy364 h) from (by
          unfold
            nb090AlphaDummy364;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0361
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠
        (nb090AlphaDummy361 A) from (by
          unfold
            nb090AlphaDummy361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0358
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy362 h) from (by
          unfold
            nb090AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0359
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy345
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠ (nb090AlphaDummy363 A) from (by
          unfold
            nb090AlphaDummy363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0360
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy364 h) from (by
          unfold
            nb090AlphaDummy364;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0361
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠
        (nb090AlphaDummy361 A) from (by
          unfold
            nb090AlphaDummy361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0358
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy362 h) from (by
          unfold
            nb090AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0359
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy345
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy353
        A) ≠ (nb090AlphaDummy365 A) from (by
          unfold
            nb090AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0364
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy366 h) from (by
          unfold
            nb090AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0365
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠
        (nb090AlphaDummy361 A) from (by
          unfold
            nb090AlphaDummy361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0362
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy362 h) from (by
          unfold
            nb090AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0363
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy353
        A) ≠ (nb090AlphaDummy365 A) from (by
          unfold
            nb090AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0364
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy366 h) from (by
          unfold
            nb090AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0365
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠
        (nb090AlphaDummy361 A) from (by
          unfold
            nb090AlphaDummy361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0362
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy362 h) from (by
          unfold
            nb090AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0363
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy349 A)
                                        from (by
                                          unfold nb090AlphaDummy349;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0346 A) 0)))) (show
                                        (nb090AlphaDummy347 h) ≠ (nb090AlphaDummy350 h)
                                        from (by
                                          unfold nb090AlphaDummy350;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0347 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy349 A), (nb090AlphaDummy350 h)),
                                      ((nb090AlphaDummy345 A), (nb090AlphaDummy347 h)),
                                      ((nb090AlphaDummy346 A), (nb090AlphaDummy348 h)),
                                      ((nb090AlphaDummy338 A), (nb090AlphaDummy340 h)),
                                      ((nb090AlphaDummy337 A), (nb090AlphaDummy339 h)),
                                      ((nb090AlphaDummy343 A), (nb090AlphaDummy344 h)),
                                      ((nb090AlphaDummy341 A), (nb090AlphaDummy342 h)),
                                      ((nb090AlphaDummy334 A), (nb090AlphaDummy336 h)),
                                      ((nb090AlphaDummy333 A), (nb090AlphaDummy335 h)),
                                      ((nb090AlphaDummy331 A), (nb090AlphaDummy332 v h)),
                                      ((nb090AlphaDummy329 A), (nb090AlphaDummy330 v h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy349 A) from
                                      (by
                                        unfold nb090AlphaDummy349;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0346 A)
                                                0)))) (show (nb090AlphaDummy347 h) ≠
                                        (nb090AlphaDummy350 h) from (by
                                        unfold nb090AlphaDummy350;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0347 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy349 A)
                                        from (by
                                          unfold nb090AlphaDummy349;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0346 A) 0)))) (show
                                        (nb090AlphaDummy347 h) ≠ (nb090AlphaDummy350 h)
                                        from (by
                                          unfold nb090AlphaDummy350;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0347 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy349 A), (nb090AlphaDummy350 h)),
                                      ((nb090AlphaDummy345 A), (nb090AlphaDummy347 h)),
                                      ((nb090AlphaDummy346 A), (nb090AlphaDummy348 h)),
                                      ((nb090AlphaDummy338 A), (nb090AlphaDummy340 h)),
                                      ((nb090AlphaDummy337 A), (nb090AlphaDummy339 h)),
                                      ((nb090AlphaDummy343 A), (nb090AlphaDummy344 h)),
                                      ((nb090AlphaDummy341 A), (nb090AlphaDummy342 h)),
                                      ((nb090AlphaDummy334 A), (nb090AlphaDummy336 h)),
                                      ((nb090AlphaDummy333 A), (nb090AlphaDummy335 h)),
                                      ((nb090AlphaDummy331 A), (nb090AlphaDummy332 v h)),
                                      ((nb090AlphaDummy329 A), (nb090AlphaDummy330 v h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part055`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0032`. -/
@[expose]
noncomputable def nb090SplitAlpha0032 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy369 A), (nb090AlphaDummy370 h)),
        ((nb090AlphaDummy338 A), (nb090AlphaDummy340 h)),
        ((nb090AlphaDummy337 A), (nb090AlphaDummy339 h)),
        ((nb090AlphaDummy367 A), (nb090AlphaDummy368 h)),
        ((nb090AlphaDummy341 A), (nb090AlphaDummy342 h)),
        ((nb090AlphaDummy334 A), (nb090AlphaDummy336 h)),
        ((nb090AlphaDummy333 A), (nb090AlphaDummy335 h)),
        ((nb090AlphaDummy331 A), (nb090AlphaDummy332 v h)),
        ((nb090AlphaDummy329 A), (nb090AlphaDummy330 v h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy369 A))
          (synCcompl (synCphi (Class.cv (nb090AlphaDummy338 A))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy369 A)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy370 h))
          (synCcompl (synCphi (Class.cv (nb090AlphaDummy340 h))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy370 h))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy338 A) ≠ (nb090AlphaDummy345 A) from (by
                              unfold nb090AlphaDummy345;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0344 A) 0))))
                          (show (nb090AlphaDummy340 h) ≠ (nb090AlphaDummy347 h) from (by
                              unfold nb090AlphaDummy347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0345 h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy338 A) ≠ (nb090AlphaDummy346 A) from (by
                                unfold nb090AlphaDummy346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0344 A) 1))))
                            (show (nb090AlphaDummy340 h) ≠ (nb090AlphaDummy348 h) from (by
                                unfold nb090AlphaDummy348;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0345 h) 1))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy338 A) ≠ (nb090AlphaDummy371 A) from
                                (by
                                  unfold nb090AlphaDummy371;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0374 A) 0))))
                              (show (nb090AlphaDummy340 h) ≠ (nb090AlphaDummy372 h) from
                                (by
                                  unfold nb090AlphaDummy372;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0375 h) 0))))
                              (TAlphaVar.there (show
                                  (nb090AlphaDummy338 A) ≠ (nb090AlphaDummy369 A) from (by
                                    unfold nb090AlphaDummy369;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0372 A)
                                            0)))) (show
                                  (nb090AlphaDummy340 h) ≠ (nb090AlphaDummy370 h) from (by
                                    unfold nb090AlphaDummy370;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0373 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy338 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy340 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy352 A) from (by
          unfold nb090AlphaDummy352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0348 A) 1)))) (show (nb090AlphaDummy347 h) ≠
        (nb090AlphaDummy355 h) from (by
          unfold nb090AlphaDummy355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy351 A) from (by
          unfold nb090AlphaDummy351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0348 A) 0)))) (show (nb090AlphaDummy347 h) ≠
        (nb090AlphaDummy354 h) from (by
          unfold nb090AlphaDummy354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy349 A) from (by
          unfold nb090AlphaDummy349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346 A)
                  0)))) (show (nb090AlphaDummy347 h) ≠ (nb090AlphaDummy350 h) from (by
          unfold nb090AlphaDummy350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy353 A), (nb090AlphaDummy356 h)), ((nb090AlphaDummy352 A),
        (nb090AlphaDummy355 h)), ((nb090AlphaDummy351 A), (nb090AlphaDummy354 h)),
        ((nb090AlphaDummy349 A), (nb090AlphaDummy350 h)), ((nb090AlphaDummy345 A),
        (nb090AlphaDummy347 h)), ((nb090AlphaDummy346 A), (nb090AlphaDummy348 h)),
        ((nb090AlphaDummy371 A), (nb090AlphaDummy372 h)), ((nb090AlphaDummy369 A),
        (nb090AlphaDummy370 h)), ((nb090AlphaDummy338 A), (nb090AlphaDummy340 h)),
        ((nb090AlphaDummy337 A), (nb090AlphaDummy339 h)), ((nb090AlphaDummy367 A),
        (nb090AlphaDummy368 h)), ((nb090AlphaDummy341 A), (nb090AlphaDummy342 h)),
        ((nb090AlphaDummy334 A), (nb090AlphaDummy336 h)), ((nb090AlphaDummy333 A),
        (nb090AlphaDummy335 h)), ((nb090AlphaDummy331 A), (nb090AlphaDummy332 v h)),
        ((nb090AlphaDummy329 A), (nb090AlphaDummy330 v h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy352
        A) ≠ (nb090AlphaDummy359 A) from (by
          unfold
            nb090AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0352
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy360 h) from (by
          unfold
            nb090AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0353
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠
        (nb090AlphaDummy357 A) from (by
          unfold
            nb090AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0350
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy358 h) from (by
          unfold
            nb090AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0351
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy345
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠ (nb090AlphaDummy359 A) from (by
          unfold
            nb090AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0356
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy360 h) from (by
          unfold
            nb090AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0357
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠
        (nb090AlphaDummy357 A) from (by
          unfold
            nb090AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0354
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy358 h) from (by
          unfold
            nb090AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0355
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠ (nb090AlphaDummy359 A) from (by
          unfold
            nb090AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0352
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy360 h) from (by
          unfold
            nb090AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0353
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠
        (nb090AlphaDummy357 A) from (by
          unfold
            nb090AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0350
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy358 h) from (by
          unfold
            nb090AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0351
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy345
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠ (nb090AlphaDummy359 A) from (by
          unfold
            nb090AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0356
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy360 h) from (by
          unfold
            nb090AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0357
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠
        (nb090AlphaDummy357 A) from (by
          unfold
            nb090AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0354
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy358 h) from (by
          unfold
            nb090AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0355
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy353 A), (nb090AlphaDummy356 h)), ((nb090AlphaDummy352 A),
        (nb090AlphaDummy355 h)), ((nb090AlphaDummy351 A), (nb090AlphaDummy354 h)),
        ((nb090AlphaDummy349 A), (nb090AlphaDummy350 h)), ((nb090AlphaDummy345 A),
        (nb090AlphaDummy347 h)), ((nb090AlphaDummy346 A), (nb090AlphaDummy348 h)),
        ((nb090AlphaDummy371 A), (nb090AlphaDummy372 h)), ((nb090AlphaDummy369 A),
        (nb090AlphaDummy370 h)), ((nb090AlphaDummy338 A), (nb090AlphaDummy340 h)),
        ((nb090AlphaDummy337 A), (nb090AlphaDummy339 h)), ((nb090AlphaDummy367 A),
        (nb090AlphaDummy368 h)), ((nb090AlphaDummy341 A), (nb090AlphaDummy342 h)),
        ((nb090AlphaDummy334 A), (nb090AlphaDummy336 h)), ((nb090AlphaDummy333 A),
        (nb090AlphaDummy335 h)), ((nb090AlphaDummy331 A), (nb090AlphaDummy332 v h)),
        ((nb090AlphaDummy329 A), (nb090AlphaDummy330 v h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy345 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy345 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy347
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠ (nb090AlphaDummy363 A) from (by
          unfold
            nb090AlphaDummy363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0360
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy364 h) from (by
          unfold
            nb090AlphaDummy364;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0361
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠
        (nb090AlphaDummy361 A) from (by
          unfold
            nb090AlphaDummy361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0358
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy362 h) from (by
          unfold
            nb090AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0359
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy345
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠ (nb090AlphaDummy363 A) from (by
          unfold
            nb090AlphaDummy363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0360
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy364 h) from (by
          unfold
            nb090AlphaDummy364;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0361
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠
        (nb090AlphaDummy361 A) from (by
          unfold
            nb090AlphaDummy361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0358
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy362 h) from (by
          unfold
            nb090AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0359
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy345
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy353
        A) ≠ (nb090AlphaDummy365 A) from (by
          unfold
            nb090AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0364
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy366 h) from (by
          unfold
            nb090AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0365
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠
        (nb090AlphaDummy361 A) from (by
          unfold
            nb090AlphaDummy361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0362
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy362 h) from (by
          unfold
            nb090AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0363
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy353
        A) ≠ (nb090AlphaDummy365 A) from (by
          unfold
            nb090AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0364
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy366 h) from (by
          unfold
            nb090AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0365
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠
        (nb090AlphaDummy361 A) from (by
          unfold
            nb090AlphaDummy361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0362
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy362 h) from (by
          unfold
            nb090AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0363
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy349 A) from
                                      (by
                                        unfold nb090AlphaDummy349;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0346 A)
                                                0)))) (show (nb090AlphaDummy347 h) ≠
                                        (nb090AlphaDummy350 h) from (by
                                        unfold nb090AlphaDummy350;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0347 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy349 A), (nb090AlphaDummy350 h)),
                                    ((nb090AlphaDummy345 A), (nb090AlphaDummy347 h)),
                                    ((nb090AlphaDummy346 A), (nb090AlphaDummy348 h)),
                                    ((nb090AlphaDummy371 A), (nb090AlphaDummy372 h)),
                                    ((nb090AlphaDummy369 A), (nb090AlphaDummy370 h)),
                                    ((nb090AlphaDummy338 A), (nb090AlphaDummy340 h)),
                                    ((nb090AlphaDummy337 A), (nb090AlphaDummy339 h)),
                                    ((nb090AlphaDummy367 A), (nb090AlphaDummy368 h)),
                                    ((nb090AlphaDummy341 A), (nb090AlphaDummy342 h)),
                                    ((nb090AlphaDummy334 A), (nb090AlphaDummy336 h)),
                                    ((nb090AlphaDummy333 A), (nb090AlphaDummy335 h)),
                                    ((nb090AlphaDummy331 A), (nb090AlphaDummy332 v h)),
                                    ((nb090AlphaDummy329 A), (nb090AlphaDummy330 v h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy349 A) from
                                    (by
                                      unfold nb090AlphaDummy349;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0346 A)
                                              0)))) (show
                                    (nb090AlphaDummy347 h) ≠ (nb090AlphaDummy350 h) from
                                    (by
                                      unfold nb090AlphaDummy350;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0347 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy349 A) from
                                      (by
                                        unfold nb090AlphaDummy349;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0346 A)
                                                0)))) (show (nb090AlphaDummy347 h) ≠
                                        (nb090AlphaDummy350 h) from (by
                                        unfold nb090AlphaDummy350;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0347 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy349 A), (nb090AlphaDummy350 h)),
                                    ((nb090AlphaDummy345 A), (nb090AlphaDummy347 h)),
                                    ((nb090AlphaDummy346 A), (nb090AlphaDummy348 h)),
                                    ((nb090AlphaDummy371 A), (nb090AlphaDummy372 h)),
                                    ((nb090AlphaDummy369 A), (nb090AlphaDummy370 h)),
                                    ((nb090AlphaDummy338 A), (nb090AlphaDummy340 h)),
                                    ((nb090AlphaDummy337 A), (nb090AlphaDummy339 h)),
                                    ((nb090AlphaDummy367 A), (nb090AlphaDummy368 h)),
                                    ((nb090AlphaDummy341 A), (nb090AlphaDummy342 h)),
                                    ((nb090AlphaDummy334 A), (nb090AlphaDummy336 h)),
                                    ((nb090AlphaDummy333 A), (nb090AlphaDummy335 h)),
                                    ((nb090AlphaDummy331 A), (nb090AlphaDummy332 v h)),
                                    ((nb090AlphaDummy329 A), (nb090AlphaDummy330 v h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy338 A) ≠ (nb090AlphaDummy345 A) from (by
                              unfold nb090AlphaDummy345;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0344 A) 0))))
                          (show (nb090AlphaDummy340 h) ≠ (nb090AlphaDummy347 h) from (by
                              unfold nb090AlphaDummy347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0345 h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy338 A) ≠ (nb090AlphaDummy346 A) from (by
                                unfold nb090AlphaDummy346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0344 A) 1))))
                            (show (nb090AlphaDummy340 h) ≠ (nb090AlphaDummy348 h) from (by
                                unfold nb090AlphaDummy348;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0345 h) 1))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy338 A) ≠ (nb090AlphaDummy371 A) from
                                (by
                                  unfold nb090AlphaDummy371;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0374 A) 0))))
                              (show (nb090AlphaDummy340 h) ≠ (nb090AlphaDummy372 h) from
                                (by
                                  unfold nb090AlphaDummy372;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0375 h) 0))))
                              (TAlphaVar.there (show
                                  (nb090AlphaDummy338 A) ≠ (nb090AlphaDummy369 A) from (by
                                    unfold nb090AlphaDummy369;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0372 A)
                                            0)))) (show
                                  (nb090AlphaDummy340 h) ≠ (nb090AlphaDummy370 h) from (by
                                    unfold nb090AlphaDummy370;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0373 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy338 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy340 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy352 A) from (by
          unfold nb090AlphaDummy352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0348 A) 1)))) (show (nb090AlphaDummy347 h) ≠
        (nb090AlphaDummy355 h) from (by
          unfold nb090AlphaDummy355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy351 A) from (by
          unfold nb090AlphaDummy351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0348 A) 0)))) (show (nb090AlphaDummy347 h) ≠
        (nb090AlphaDummy354 h) from (by
          unfold nb090AlphaDummy354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy349 A) from (by
          unfold nb090AlphaDummy349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346 A)
                  0)))) (show (nb090AlphaDummy347 h) ≠ (nb090AlphaDummy350 h) from (by
          unfold nb090AlphaDummy350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy353 A), (nb090AlphaDummy356 h)), ((nb090AlphaDummy352 A),
        (nb090AlphaDummy355 h)), ((nb090AlphaDummy351 A), (nb090AlphaDummy354 h)),
        ((nb090AlphaDummy349 A), (nb090AlphaDummy350 h)), ((nb090AlphaDummy345 A),
        (nb090AlphaDummy347 h)), ((nb090AlphaDummy346 A), (nb090AlphaDummy348 h)),
        ((nb090AlphaDummy371 A), (nb090AlphaDummy372 h)), ((nb090AlphaDummy369 A),
        (nb090AlphaDummy370 h)), ((nb090AlphaDummy338 A), (nb090AlphaDummy340 h)),
        ((nb090AlphaDummy337 A), (nb090AlphaDummy339 h)), ((nb090AlphaDummy367 A),
        (nb090AlphaDummy368 h)), ((nb090AlphaDummy341 A), (nb090AlphaDummy342 h)),
        ((nb090AlphaDummy334 A), (nb090AlphaDummy336 h)), ((nb090AlphaDummy333 A),
        (nb090AlphaDummy335 h)), ((nb090AlphaDummy331 A), (nb090AlphaDummy332 v h)),
        ((nb090AlphaDummy329 A), (nb090AlphaDummy330 v h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy352
        A) ≠ (nb090AlphaDummy359 A) from (by
          unfold
            nb090AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0352
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy360 h) from (by
          unfold
            nb090AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0353
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠
        (nb090AlphaDummy357 A) from (by
          unfold
            nb090AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0350
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy358 h) from (by
          unfold
            nb090AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0351
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy345
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠ (nb090AlphaDummy359 A) from (by
          unfold
            nb090AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0356
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy360 h) from (by
          unfold
            nb090AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0357
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠
        (nb090AlphaDummy357 A) from (by
          unfold
            nb090AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0354
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy358 h) from (by
          unfold
            nb090AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0355
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠ (nb090AlphaDummy359 A) from (by
          unfold
            nb090AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0352
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy360 h) from (by
          unfold
            nb090AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0353
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠
        (nb090AlphaDummy357 A) from (by
          unfold
            nb090AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0350
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy358 h) from (by
          unfold
            nb090AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0351
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy345
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠ (nb090AlphaDummy359 A) from (by
          unfold
            nb090AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0356
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy360 h) from (by
          unfold
            nb090AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0357
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠
        (nb090AlphaDummy357 A) from (by
          unfold
            nb090AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0354
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy358 h) from (by
          unfold
            nb090AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0355
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy353 A), (nb090AlphaDummy356 h)), ((nb090AlphaDummy352 A),
        (nb090AlphaDummy355 h)), ((nb090AlphaDummy351 A), (nb090AlphaDummy354 h)),
        ((nb090AlphaDummy349 A), (nb090AlphaDummy350 h)), ((nb090AlphaDummy345 A),
        (nb090AlphaDummy347 h)), ((nb090AlphaDummy346 A), (nb090AlphaDummy348 h)),
        ((nb090AlphaDummy371 A), (nb090AlphaDummy372 h)), ((nb090AlphaDummy369 A),
        (nb090AlphaDummy370 h)), ((nb090AlphaDummy338 A), (nb090AlphaDummy340 h)),
        ((nb090AlphaDummy337 A), (nb090AlphaDummy339 h)), ((nb090AlphaDummy367 A),
        (nb090AlphaDummy368 h)), ((nb090AlphaDummy341 A), (nb090AlphaDummy342 h)),
        ((nb090AlphaDummy334 A), (nb090AlphaDummy336 h)), ((nb090AlphaDummy333 A),
        (nb090AlphaDummy335 h)), ((nb090AlphaDummy331 A), (nb090AlphaDummy332 v h)),
        ((nb090AlphaDummy329 A), (nb090AlphaDummy330 v h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy345 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy345 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy347
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠ (nb090AlphaDummy363 A) from (by
          unfold
            nb090AlphaDummy363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0360
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy364 h) from (by
          unfold
            nb090AlphaDummy364;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0361
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠
        (nb090AlphaDummy361 A) from (by
          unfold
            nb090AlphaDummy361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0358
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy362 h) from (by
          unfold
            nb090AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0359
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy345
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠ (nb090AlphaDummy363 A) from (by
          unfold
            nb090AlphaDummy363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0360
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy364 h) from (by
          unfold
            nb090AlphaDummy364;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0361
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy352 A) ≠
        (nb090AlphaDummy361 A) from (by
          unfold
            nb090AlphaDummy361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0358
                    A)
                  0)))) (show (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy362 h) from (by
          unfold
            nb090AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0359
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy345
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy353
        A) ≠ (nb090AlphaDummy365 A) from (by
          unfold
            nb090AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0364
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy366 h) from (by
          unfold
            nb090AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0365
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠
        (nb090AlphaDummy361 A) from (by
          unfold
            nb090AlphaDummy361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0362
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy362 h) from (by
          unfold
            nb090AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0363
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy353
        A) ≠ (nb090AlphaDummy365 A) from (by
          unfold
            nb090AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0364
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy366 h) from (by
          unfold
            nb090AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0365
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy353 A) ≠
        (nb090AlphaDummy361 A) from (by
          unfold
            nb090AlphaDummy361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0362
                    A)
                  0)))) (show (nb090AlphaDummy356 h) ≠ (nb090AlphaDummy362 h) from (by
          unfold
            nb090AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0363
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy349 A) from
                                      (by
                                        unfold nb090AlphaDummy349;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0346 A)
                                                0)))) (show (nb090AlphaDummy347 h) ≠
                                        (nb090AlphaDummy350 h) from (by
                                        unfold nb090AlphaDummy350;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0347 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy349 A), (nb090AlphaDummy350 h)),
                                    ((nb090AlphaDummy345 A), (nb090AlphaDummy347 h)),
                                    ((nb090AlphaDummy346 A), (nb090AlphaDummy348 h)),
                                    ((nb090AlphaDummy371 A), (nb090AlphaDummy372 h)),
                                    ((nb090AlphaDummy369 A), (nb090AlphaDummy370 h)),
                                    ((nb090AlphaDummy338 A), (nb090AlphaDummy340 h)),
                                    ((nb090AlphaDummy337 A), (nb090AlphaDummy339 h)),
                                    ((nb090AlphaDummy367 A), (nb090AlphaDummy368 h)),
                                    ((nb090AlphaDummy341 A), (nb090AlphaDummy342 h)),
                                    ((nb090AlphaDummy334 A), (nb090AlphaDummy336 h)),
                                    ((nb090AlphaDummy333 A), (nb090AlphaDummy335 h)),
                                    ((nb090AlphaDummy331 A), (nb090AlphaDummy332 v h)),
                                    ((nb090AlphaDummy329 A), (nb090AlphaDummy330 v h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy349 A) from
                                    (by
                                      unfold nb090AlphaDummy349;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0346 A)
                                              0)))) (show
                                    (nb090AlphaDummy347 h) ≠ (nb090AlphaDummy350 h) from
                                    (by
                                      unfold nb090AlphaDummy350;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0347 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy349 A) from
                                      (by
                                        unfold nb090AlphaDummy349;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0346 A)
                                                0)))) (show (nb090AlphaDummy347 h) ≠
                                        (nb090AlphaDummy350 h) from (by
                                        unfold nb090AlphaDummy350;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0347 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy349 A), (nb090AlphaDummy350 h)),
                                    ((nb090AlphaDummy345 A), (nb090AlphaDummy347 h)),
                                    ((nb090AlphaDummy346 A), (nb090AlphaDummy348 h)),
                                    ((nb090AlphaDummy371 A), (nb090AlphaDummy372 h)),
                                    ((nb090AlphaDummy369 A), (nb090AlphaDummy370 h)),
                                    ((nb090AlphaDummy338 A), (nb090AlphaDummy340 h)),
                                    ((nb090AlphaDummy337 A), (nb090AlphaDummy339 h)),
                                    ((nb090AlphaDummy367 A), (nb090AlphaDummy368 h)),
                                    ((nb090AlphaDummy341 A), (nb090AlphaDummy342 h)),
                                    ((nb090AlphaDummy334 A), (nb090AlphaDummy336 h)),
                                    ((nb090AlphaDummy333 A), (nb090AlphaDummy335 h)),
                                    ((nb090AlphaDummy331 A), (nb090AlphaDummy332 v h)),
                                    ((nb090AlphaDummy329 A), (nb090AlphaDummy330 v h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb090AlphaDummy369 A), (nb090AlphaDummy370 h)),
            ((nb090AlphaDummy338 A), (nb090AlphaDummy340 h)),
            ((nb090AlphaDummy337 A), (nb090AlphaDummy339 h)),
            ((nb090AlphaDummy367 A), (nb090AlphaDummy368 h)),
            ((nb090AlphaDummy341 A), (nb090AlphaDummy342 h)),
            ((nb090AlphaDummy334 A), (nb090AlphaDummy336 h)),
            ((nb090AlphaDummy333 A), (nb090AlphaDummy335 h)),
            ((nb090AlphaDummy331 A), (nb090AlphaDummy332 v h)),
            ((nb090AlphaDummy329 A), (nb090AlphaDummy330 v h)),
            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
            ((nb090AlphaDummy001 A), u),
            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
          (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

theorem nb090_compact_fv_empty_0300 (A : Class) :
    (nb090AlphaDummy373 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0301 (v : Var) :
    (nb090AlphaDummy374 v) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0302 (A : Class) :
    (nb090AlphaDummy375 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0303 (v : Var) :
    (nb090AlphaDummy376 v) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0304 (A : Class) :
    (nb090AlphaDummy378 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0305 (v : Var) :
    (nb090AlphaDummy380 v) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0306 (A : Class) :
    (nb090AlphaDummy377 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0307 (v : Var) :
    (nb090AlphaDummy379 v) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
