/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C095M3Part020Stage1


/-! NF weak partition development: NAR4H5C095M3Part020. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0032`. -/
@[expose]
noncomputable def nb095SplitAlpha0032 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy351 D R S_cls E), (nb095AlphaDummy352 u S_cls)),
        ((nb095AlphaDummy349 D R S_cls E), (nb095AlphaDummy350 u S_cls)),
        ((nb095AlphaDummy340 D R S_cls E), (nb095AlphaDummy342 u S_cls)),
        ((nb095AlphaDummy339 D R S_cls E), (nb095AlphaDummy341 u S_cls)),
        ((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy351 D R S_cls E))
          (Class.cab (nb095AlphaDummy345 D R S_cls E)
            (synWrex (nb095AlphaDummy346 D R S_cls E)
              (Class.cv (nb095AlphaDummy340 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy351 D R S_cls E))
            (Class.cab (nb095AlphaDummy345 D R S_cls E)
              (synWrex (nb095AlphaDummy346 D R S_cls E)
                (Class.cv (nb095AlphaDummy340 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy352 u S_cls))
          (Class.cab (nb095AlphaDummy347 u S_cls) (synWrex (nb095AlphaDummy348 u S_cls)
              (Class.cv (nb095AlphaDummy342 u S_cls))
              (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
                (synCphi (Class.cv (nb095AlphaDummy348 u S_cls))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy352 u S_cls))
            (Class.cab (nb095AlphaDummy347 u S_cls) (synWrex (nb095AlphaDummy348 u S_cls)
                (Class.cv (nb095AlphaDummy342 u S_cls))
                (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
                  (synCphi (Class.cv (nb095AlphaDummy348 u S_cls))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy340 D R S_cls E) ≠
                      (nb095AlphaDummy346 D R S_cls E) from (by
                      unfold nb095AlphaDummy346;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0352 D R S_cls E) 1))))
                  (show (nb095AlphaDummy342 u S_cls) ≠ (nb095AlphaDummy348 u S_cls) from
                    (by
                      unfold nb095AlphaDummy348;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0354 u S_cls) 1))))
                  (TAlphaVar.there (show (nb095AlphaDummy340 D R S_cls E) ≠
                        (nb095AlphaDummy345 D R S_cls E) from (by
                        unfold nb095AlphaDummy345;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0352 D R S_cls E) 0)))) (show
                      (nb095AlphaDummy342 u S_cls) ≠ (nb095AlphaDummy347 u S_cls) from (by
                        unfold nb095AlphaDummy347;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0354 u S_cls) 0))))
                    (TAlphaVar.there (show (nb095AlphaDummy340 D R S_cls E) ≠
                          (nb095AlphaDummy351 D R S_cls E) from (by
                          unfold nb095AlphaDummy351;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0356 D R S_cls E)
                                  0)))) (show
                        (nb095AlphaDummy342 u S_cls) ≠ (nb095AlphaDummy352 u S_cls) from
                        (by
                          unfold nb095AlphaDummy352;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0357 u S_cls) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy340 D R S_cls E) ≠
                            (nb095AlphaDummy349 D R S_cls E) from (by
                            unfold nb095AlphaDummy349;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0353 D R S_cls E)
                                    0)))) (show (nb095AlphaDummy342 u S_cls) ≠
                            (nb095AlphaDummy350 u S_cls) from (by
                            unfold nb095AlphaDummy350;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0355 u S_cls) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy340 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪
                      ((Class.cv (nb095AlphaDummy341 u S_cls))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy346 D R S_cls E) ≠
                              (nb095AlphaDummy353 D R S_cls E) from (by
                              unfold nb095AlphaDummy353;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0358 D R S_cls E)
                                      0)))) (show (nb095AlphaDummy348 u S_cls) ≠
                              (nb095AlphaDummy355 u S_cls) from (by
                              unfold nb095AlphaDummy355;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0359 u S_cls)
                                      0)))) (TAlphaVar.there (show
                              (nb095AlphaDummy346 D R S_cls E) ≠
                                (nb095AlphaDummy354 D R S_cls E) from (by
                                unfold nb095AlphaDummy354;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0358 D R S_cls E) 1)))) (show
                              (nb095AlphaDummy348 u S_cls) ≠ (nb095AlphaDummy356 u S_cls)
                              from (by
                                unfold nb095AlphaDummy356;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0359 u S_cls)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy346 D R S_cls E))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb095AlphaDummy348 u S_cls))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy353 D R S_cls E) ≠
        (nb095AlphaDummy360 D R S_cls E) from (by
          unfold nb095AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0362 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy355 u S_cls) ≠ (nb095AlphaDummy363 u S_cls)
        from (by
          unfold nb095AlphaDummy363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0363 u S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy353 D R S_cls E) ≠
        (nb095AlphaDummy359 D R S_cls E) from (by
          unfold nb095AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0362 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy355 u S_cls) ≠ (nb095AlphaDummy362 u S_cls)
        from (by
          unfold nb095AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0363 u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy353 D R S_cls E) ≠
        (nb095AlphaDummy357 D R S_cls E) from (by
          unfold nb095AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0360 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy355 u S_cls) ≠ (nb095AlphaDummy358 u S_cls)
        from (by
          unfold nb095AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0361 u
                    S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy361 D R S_cls E), (nb095AlphaDummy364 u S_cls)),
        ((nb095AlphaDummy360 D R S_cls E), (nb095AlphaDummy363 u S_cls)),
        ((nb095AlphaDummy359 D R S_cls E), (nb095AlphaDummy362 u S_cls)),
        ((nb095AlphaDummy357 D R S_cls E), (nb095AlphaDummy358 u S_cls)),
        ((nb095AlphaDummy353 D R S_cls E), (nb095AlphaDummy355 u S_cls)),
        ((nb095AlphaDummy354 D R S_cls E), (nb095AlphaDummy356 u S_cls)),
        ((nb095AlphaDummy346 D R S_cls E), (nb095AlphaDummy348 u S_cls)),
        ((nb095AlphaDummy345 D R S_cls E), (nb095AlphaDummy347 u S_cls)),
        ((nb095AlphaDummy351 D R S_cls E), (nb095AlphaDummy352 u S_cls)),
        ((nb095AlphaDummy349 D R S_cls E), (nb095AlphaDummy350 u S_cls)),
        ((nb095AlphaDummy340 D R S_cls E), (nb095AlphaDummy342 u S_cls)),
        ((nb095AlphaDummy339 D R S_cls E), (nb095AlphaDummy341 u S_cls)),
        ((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy360
        D R S_cls E) ≠ (nb095AlphaDummy367 D R S_cls E) from (by
          unfold
            nb095AlphaDummy367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0366
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy368 u S_cls)
        from (by
          unfold
            nb095AlphaDummy368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0367
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠
        (nb095AlphaDummy365 D R S_cls E) from (by
          unfold
            nb095AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0364
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy366 u S_cls)
        from (by
          unfold
            nb095AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0365
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy353
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠ (nb095AlphaDummy367
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0370
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy368 u S_cls)
        from (by
          unfold
            nb095AlphaDummy368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0371
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠
        (nb095AlphaDummy365 D R S_cls E) from (by
          unfold
            nb095AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0368
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy366 u S_cls)
        from (by
          unfold
            nb095AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0369
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠ (nb095AlphaDummy367
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0366
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy368 u S_cls)
        from (by
          unfold
            nb095AlphaDummy368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0367
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠
        (nb095AlphaDummy365 D R S_cls E) from (by
          unfold
            nb095AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0364
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy366 u S_cls)
        from (by
          unfold
            nb095AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0365
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy353
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠ (nb095AlphaDummy367
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0370
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy368 u S_cls)
        from (by
          unfold
            nb095AlphaDummy368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0371
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠
        (nb095AlphaDummy365 D R S_cls E) from (by
          unfold
            nb095AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0368
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy366 u S_cls)
        from (by
          unfold
            nb095AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0369
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy361 D R S_cls E), (nb095AlphaDummy364 u S_cls)),
        ((nb095AlphaDummy360 D R S_cls E), (nb095AlphaDummy363 u S_cls)),
        ((nb095AlphaDummy359 D R S_cls E), (nb095AlphaDummy362 u S_cls)),
        ((nb095AlphaDummy357 D R S_cls E), (nb095AlphaDummy358 u S_cls)),
        ((nb095AlphaDummy353 D R S_cls E), (nb095AlphaDummy355 u S_cls)),
        ((nb095AlphaDummy354 D R S_cls E), (nb095AlphaDummy356 u S_cls)),
        ((nb095AlphaDummy346 D R S_cls E), (nb095AlphaDummy348 u S_cls)),
        ((nb095AlphaDummy345 D R S_cls E), (nb095AlphaDummy347 u S_cls)),
        ((nb095AlphaDummy351 D R S_cls E), (nb095AlphaDummy352 u S_cls)),
        ((nb095AlphaDummy349 D R S_cls E), (nb095AlphaDummy350 u S_cls)),
        ((nb095AlphaDummy340 D R S_cls E), (nb095AlphaDummy342 u S_cls)),
        ((nb095AlphaDummy339 D R S_cls E), (nb095AlphaDummy341 u S_cls)),
        ((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy353 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy353 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy360
        D R S_cls E) ≠ (nb095AlphaDummy371 D R S_cls E) from (by
          unfold
            nb095AlphaDummy371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0374
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy372 u S_cls)
        from (by
          unfold
            nb095AlphaDummy372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0375
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠
        (nb095AlphaDummy369 D R S_cls E) from (by
          unfold
            nb095AlphaDummy369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0372
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy370 u S_cls)
        from (by
          unfold
            nb095AlphaDummy370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0373
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy353
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠ (nb095AlphaDummy371
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0374
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy372 u S_cls)
        from (by
          unfold
            nb095AlphaDummy372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0375
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠
        (nb095AlphaDummy369 D R S_cls E) from (by
          unfold
            nb095AlphaDummy369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0372
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy370 u S_cls)
        from (by
          unfold
            nb095AlphaDummy370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0373
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy353
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy361
        D R S_cls E) ≠ (nb095AlphaDummy373 D R S_cls E) from (by
          unfold
            nb095AlphaDummy373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0378
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy374 u S_cls)
        from (by
          unfold
            nb095AlphaDummy374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0379
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠
        (nb095AlphaDummy369 D R S_cls E) from (by
          unfold
            nb095AlphaDummy369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0376
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy370 u S_cls)
        from (by
          unfold
            nb095AlphaDummy370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0377
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy361
        D R S_cls E) ≠ (nb095AlphaDummy373 D R S_cls E) from (by
          unfold
            nb095AlphaDummy373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0378
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy374 u S_cls)
        from (by
          unfold
            nb095AlphaDummy374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0379
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠
        (nb095AlphaDummy369 D R S_cls E) from (by
          unfold
            nb095AlphaDummy369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0376
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy370 u S_cls)
        from (by
          unfold
            nb095AlphaDummy370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0377
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy353 D R S_cls E) ≠
                                        (nb095AlphaDummy357 D R S_cls E) from (by
                                        unfold nb095AlphaDummy357;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy355 u S_cls) ≠
                                        (nb095AlphaDummy358 u S_cls) from (by
                                        unfold nb095AlphaDummy358;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0361 u S_cls) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy357 D R S_cls E),
                                      (nb095AlphaDummy358 u S_cls)),
                                    ((nb095AlphaDummy353 D R S_cls E),
                                      (nb095AlphaDummy355 u S_cls)),
                                    ((nb095AlphaDummy354 D R S_cls E),
                                      (nb095AlphaDummy356 u S_cls)),
                                    ((nb095AlphaDummy346 D R S_cls E),
                                      (nb095AlphaDummy348 u S_cls)),
                                    ((nb095AlphaDummy345 D R S_cls E),
                                      (nb095AlphaDummy347 u S_cls)),
                                    ((nb095AlphaDummy351 D R S_cls E),
                                      (nb095AlphaDummy352 u S_cls)),
                                    ((nb095AlphaDummy349 D R S_cls E),
                                      (nb095AlphaDummy350 u S_cls)),
                                    ((nb095AlphaDummy340 D R S_cls E),
                                      (nb095AlphaDummy342 u S_cls)),
                                    ((nb095AlphaDummy339 D R S_cls E),
                                      (nb095AlphaDummy341 u S_cls)),
                                    ((nb095AlphaDummy337 D R S_cls E),
                                      (nb095AlphaDummy338 u S_cls E)),
                                    ((nb095AlphaDummy335 D R S_cls E),
                                      (nb095AlphaDummy336 u S_cls E)),
                                    ((nb095AlphaDummy293 D R S_cls E),
                                      (nb095AlphaDummy294 u S_cls f E)),
                                    ((nb095AlphaDummy291 D R S_cls E),
                                      (nb095AlphaDummy292 u S_cls f E)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy353 D R S_cls E) ≠
                                      (nb095AlphaDummy357 D R S_cls E) from (by
                                      unfold nb095AlphaDummy357;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy355 u S_cls) ≠
                                      (nb095AlphaDummy358 u S_cls) from (by
                                      unfold nb095AlphaDummy358;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0361 u S_cls) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy353 D R S_cls E) ≠
                                        (nb095AlphaDummy357 D R S_cls E) from (by
                                        unfold nb095AlphaDummy357;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy355 u S_cls) ≠
                                        (nb095AlphaDummy358 u S_cls) from (by
                                        unfold nb095AlphaDummy358;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0361 u S_cls) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy357 D R S_cls E),
                                      (nb095AlphaDummy358 u S_cls)),
                                    ((nb095AlphaDummy353 D R S_cls E),
                                      (nb095AlphaDummy355 u S_cls)),
                                    ((nb095AlphaDummy354 D R S_cls E),
                                      (nb095AlphaDummy356 u S_cls)),
                                    ((nb095AlphaDummy346 D R S_cls E),
                                      (nb095AlphaDummy348 u S_cls)),
                                    ((nb095AlphaDummy345 D R S_cls E),
                                      (nb095AlphaDummy347 u S_cls)),
                                    ((nb095AlphaDummy351 D R S_cls E),
                                      (nb095AlphaDummy352 u S_cls)),
                                    ((nb095AlphaDummy349 D R S_cls E),
                                      (nb095AlphaDummy350 u S_cls)),
                                    ((nb095AlphaDummy340 D R S_cls E),
                                      (nb095AlphaDummy342 u S_cls)),
                                    ((nb095AlphaDummy339 D R S_cls E),
                                      (nb095AlphaDummy341 u S_cls)),
                                    ((nb095AlphaDummy337 D R S_cls E),
                                      (nb095AlphaDummy338 u S_cls E)),
                                    ((nb095AlphaDummy335 D R S_cls E),
                                      (nb095AlphaDummy336 u S_cls E)),
                                    ((nb095AlphaDummy293 D R S_cls E),
                                      (nb095AlphaDummy294 u S_cls f E)),
                                    ((nb095AlphaDummy291 D R S_cls E),
                                      (nb095AlphaDummy292 u S_cls f E)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095AlphaDummy340 D R S_cls E) ≠
                        (nb095AlphaDummy346 D R S_cls E) from (by
                        unfold nb095AlphaDummy346;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0352 D R S_cls E) 1)))) (show
                      (nb095AlphaDummy342 u S_cls) ≠ (nb095AlphaDummy348 u S_cls) from (by
                        unfold nb095AlphaDummy348;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0354 u S_cls) 1))))
                    (TAlphaVar.there (show (nb095AlphaDummy340 D R S_cls E) ≠
                          (nb095AlphaDummy345 D R S_cls E) from (by
                          unfold nb095AlphaDummy345;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0352 D R S_cls E)
                                  0)))) (show
                        (nb095AlphaDummy342 u S_cls) ≠ (nb095AlphaDummy347 u S_cls) from
                        (by
                          unfold nb095AlphaDummy347;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0354 u S_cls) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy340 D R S_cls E) ≠
                            (nb095AlphaDummy351 D R S_cls E) from (by
                            unfold nb095AlphaDummy351;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0356 D R S_cls E)
                                    0)))) (show (nb095AlphaDummy342 u S_cls) ≠
                            (nb095AlphaDummy352 u S_cls) from (by
                            unfold nb095AlphaDummy352;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0357 u S_cls) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy340 D R S_cls E) ≠
                              (nb095AlphaDummy349 D R S_cls E) from (by
                              unfold nb095AlphaDummy349;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0353 D R S_cls E)
                                      0)))) (show (nb095AlphaDummy342 u S_cls) ≠
                              (nb095AlphaDummy350 u S_cls) from (by
                              unfold nb095AlphaDummy350;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0355 u S_cls)
                                      0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy340 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪
                        ((Class.cv (nb095AlphaDummy341 u S_cls))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy346 D R S_cls E) ≠
                                (nb095AlphaDummy353 D R S_cls E) from (by
                                unfold nb095AlphaDummy353;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0358 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy348 u S_cls) ≠ (nb095AlphaDummy355 u S_cls)
                              from (by
                                unfold nb095AlphaDummy355;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0359 u S_cls)
                                        0)))) (TAlphaVar.there (show
                                (nb095AlphaDummy346 D R S_cls E) ≠
                                  (nb095AlphaDummy354 D R S_cls E) from (by
                                  unfold nb095AlphaDummy354;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0358 D R S_cls E) 1)))) (show
                                (nb095AlphaDummy348 u S_cls) ≠
                                  (nb095AlphaDummy356 u S_cls) from (by
                                  unfold nb095AlphaDummy356;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0359 u S_cls)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy346 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy348 u S_cls))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy353 D R S_cls E) ≠ (nb095AlphaDummy360 D R S_cls E) from (by
          unfold nb095AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0362 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy355 u S_cls) ≠ (nb095AlphaDummy363 u S_cls)
        from (by
          unfold nb095AlphaDummy363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0363 u S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy353 D R S_cls E) ≠
        (nb095AlphaDummy359 D R S_cls E) from (by
          unfold nb095AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0362 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy355 u S_cls) ≠ (nb095AlphaDummy362 u S_cls)
        from (by
          unfold nb095AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0363 u
                    S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy353 D R S_cls E) ≠
        (nb095AlphaDummy357 D R S_cls E) from (by
          unfold nb095AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0360 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy355 u S_cls) ≠ (nb095AlphaDummy358 u S_cls)
        from (by
          unfold nb095AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0361 u
                    S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy361 D R S_cls E), (nb095AlphaDummy364 u S_cls)),
        ((nb095AlphaDummy360 D R S_cls E), (nb095AlphaDummy363 u S_cls)),
        ((nb095AlphaDummy359 D R S_cls E), (nb095AlphaDummy362 u S_cls)),
        ((nb095AlphaDummy357 D R S_cls E), (nb095AlphaDummy358 u S_cls)),
        ((nb095AlphaDummy353 D R S_cls E), (nb095AlphaDummy355 u S_cls)),
        ((nb095AlphaDummy354 D R S_cls E), (nb095AlphaDummy356 u S_cls)),
        ((nb095AlphaDummy346 D R S_cls E), (nb095AlphaDummy348 u S_cls)),
        ((nb095AlphaDummy345 D R S_cls E), (nb095AlphaDummy347 u S_cls)),
        ((nb095AlphaDummy351 D R S_cls E), (nb095AlphaDummy352 u S_cls)),
        ((nb095AlphaDummy349 D R S_cls E), (nb095AlphaDummy350 u S_cls)),
        ((nb095AlphaDummy340 D R S_cls E), (nb095AlphaDummy342 u S_cls)),
        ((nb095AlphaDummy339 D R S_cls E), (nb095AlphaDummy341 u S_cls)),
        ((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy360
        D R S_cls E) ≠ (nb095AlphaDummy367 D R S_cls E) from (by
          unfold
            nb095AlphaDummy367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0366
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy368 u S_cls)
        from (by
          unfold
            nb095AlphaDummy368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0367
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠
        (nb095AlphaDummy365 D R S_cls E) from (by
          unfold
            nb095AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0364
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy366 u S_cls)
        from (by
          unfold
            nb095AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0365
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy353
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠ (nb095AlphaDummy367
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0370
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy368 u S_cls)
        from (by
          unfold
            nb095AlphaDummy368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0371
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠
        (nb095AlphaDummy365 D R S_cls E) from (by
          unfold
            nb095AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0368
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy366 u S_cls)
        from (by
          unfold
            nb095AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0369
                    u
                    S_cls)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠ (nb095AlphaDummy367
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0366
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy368 u S_cls)
        from (by
          unfold
            nb095AlphaDummy368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0367
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠
        (nb095AlphaDummy365 D R S_cls E) from (by
          unfold
            nb095AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0364
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy366 u S_cls)
        from (by
          unfold
            nb095AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0365
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy353
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠ (nb095AlphaDummy367
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0370
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy368 u S_cls)
        from (by
          unfold
            nb095AlphaDummy368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0371
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠
        (nb095AlphaDummy365 D R S_cls E) from (by
          unfold
            nb095AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0368
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy366 u S_cls)
        from (by
          unfold
            nb095AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0369
                    u
                    S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy361 D R S_cls E), (nb095AlphaDummy364 u S_cls)),
        ((nb095AlphaDummy360 D R S_cls E), (nb095AlphaDummy363 u S_cls)),
        ((nb095AlphaDummy359 D R S_cls E), (nb095AlphaDummy362 u S_cls)),
        ((nb095AlphaDummy357 D R S_cls E), (nb095AlphaDummy358 u S_cls)),
        ((nb095AlphaDummy353 D R S_cls E), (nb095AlphaDummy355 u S_cls)),
        ((nb095AlphaDummy354 D R S_cls E), (nb095AlphaDummy356 u S_cls)),
        ((nb095AlphaDummy346 D R S_cls E), (nb095AlphaDummy348 u S_cls)),
        ((nb095AlphaDummy345 D R S_cls E), (nb095AlphaDummy347 u S_cls)),
        ((nb095AlphaDummy351 D R S_cls E), (nb095AlphaDummy352 u S_cls)),
        ((nb095AlphaDummy349 D R S_cls E), (nb095AlphaDummy350 u S_cls)),
        ((nb095AlphaDummy340 D R S_cls E), (nb095AlphaDummy342 u S_cls)),
        ((nb095AlphaDummy339 D R S_cls E), (nb095AlphaDummy341 u S_cls)),
        ((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy353 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy353 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy360
        D R S_cls E) ≠ (nb095AlphaDummy371 D R S_cls E) from (by
          unfold
            nb095AlphaDummy371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0374
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy372 u S_cls)
        from (by
          unfold
            nb095AlphaDummy372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0375
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠
        (nb095AlphaDummy369 D R S_cls E) from (by
          unfold
            nb095AlphaDummy369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0372
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy370 u S_cls)
        from (by
          unfold
            nb095AlphaDummy370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0373
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy353
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠ (nb095AlphaDummy371
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0374
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy372 u S_cls)
        from (by
          unfold
            nb095AlphaDummy372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0375
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠
        (nb095AlphaDummy369 D R S_cls E) from (by
          unfold
            nb095AlphaDummy369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0372
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy370 u S_cls)
        from (by
          unfold
            nb095AlphaDummy370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0373
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy353
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy361
        D R S_cls E) ≠ (nb095AlphaDummy373 D R S_cls E) from (by
          unfold
            nb095AlphaDummy373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0378
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy374 u S_cls)
        from (by
          unfold
            nb095AlphaDummy374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0379
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠
        (nb095AlphaDummy369 D R S_cls E) from (by
          unfold
            nb095AlphaDummy369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0376
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy370 u S_cls)
        from (by
          unfold
            nb095AlphaDummy370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0377
                    u
                    S_cls)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy361
        D R S_cls E) ≠ (nb095AlphaDummy373 D R S_cls E) from (by
          unfold
            nb095AlphaDummy373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0378
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy374 u S_cls)
        from (by
          unfold
            nb095AlphaDummy374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0379
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠
        (nb095AlphaDummy369 D R S_cls E) from (by
          unfold
            nb095AlphaDummy369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0376
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy370 u S_cls)
        from (by
          unfold
            nb095AlphaDummy370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0377
                    u
                    S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy353 D R S_cls E) ≠
        (nb095AlphaDummy357 D R S_cls E) from (by
                                          unfold nb095AlphaDummy357;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0360 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy355 u S_cls) ≠
        (nb095AlphaDummy358 u S_cls) from (by
                                          unfold nb095AlphaDummy358;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0361 u S_cls) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy357 D R S_cls E),
                                        (nb095AlphaDummy358 u S_cls)),
                                      ((nb095AlphaDummy353 D R S_cls E),
                                        (nb095AlphaDummy355 u S_cls)),
                                      ((nb095AlphaDummy354 D R S_cls E),
                                        (nb095AlphaDummy356 u S_cls)),
                                      ((nb095AlphaDummy346 D R S_cls E),
                                        (nb095AlphaDummy348 u S_cls)),
                                      ((nb095AlphaDummy345 D R S_cls E),
                                        (nb095AlphaDummy347 u S_cls)),
                                      ((nb095AlphaDummy351 D R S_cls E),
                                        (nb095AlphaDummy352 u S_cls)),
                                      ((nb095AlphaDummy349 D R S_cls E),
                                        (nb095AlphaDummy350 u S_cls)),
                                      ((nb095AlphaDummy340 D R S_cls E),
                                        (nb095AlphaDummy342 u S_cls)),
                                      ((nb095AlphaDummy339 D R S_cls E),
                                        (nb095AlphaDummy341 u S_cls)),
                                      ((nb095AlphaDummy337 D R S_cls E),
                                        (nb095AlphaDummy338 u S_cls E)),
                                      ((nb095AlphaDummy335 D R S_cls E),
                                        (nb095AlphaDummy336 u S_cls E)),
                                      ((nb095AlphaDummy293 D R S_cls E),
                                        (nb095AlphaDummy294 u S_cls f E)),
                                      ((nb095AlphaDummy291 D R S_cls E),
                                        (nb095AlphaDummy292 u S_cls f E)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy353 D R S_cls E) ≠
                                        (nb095AlphaDummy357 D R S_cls E) from (by
                                        unfold nb095AlphaDummy357;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy355 u S_cls) ≠
                                        (nb095AlphaDummy358 u S_cls) from (by
                                        unfold nb095AlphaDummy358;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0361 u S_cls) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy353 D R S_cls E) ≠
        (nb095AlphaDummy357 D R S_cls E) from (by
                                          unfold nb095AlphaDummy357;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0360 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy355 u S_cls) ≠
        (nb095AlphaDummy358 u S_cls) from (by
                                          unfold nb095AlphaDummy358;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0361 u S_cls) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy357 D R S_cls E),
                                        (nb095AlphaDummy358 u S_cls)),
                                      ((nb095AlphaDummy353 D R S_cls E),
                                        (nb095AlphaDummy355 u S_cls)),
                                      ((nb095AlphaDummy354 D R S_cls E),
                                        (nb095AlphaDummy356 u S_cls)),
                                      ((nb095AlphaDummy346 D R S_cls E),
                                        (nb095AlphaDummy348 u S_cls)),
                                      ((nb095AlphaDummy345 D R S_cls E),
                                        (nb095AlphaDummy347 u S_cls)),
                                      ((nb095AlphaDummy351 D R S_cls E),
                                        (nb095AlphaDummy352 u S_cls)),
                                      ((nb095AlphaDummy349 D R S_cls E),
                                        (nb095AlphaDummy350 u S_cls)),
                                      ((nb095AlphaDummy340 D R S_cls E),
                                        (nb095AlphaDummy342 u S_cls)),
                                      ((nb095AlphaDummy339 D R S_cls E),
                                        (nb095AlphaDummy341 u S_cls)),
                                      ((nb095AlphaDummy337 D R S_cls E),
                                        (nb095AlphaDummy338 u S_cls E)),
                                      ((nb095AlphaDummy335 D R S_cls E),
                                        (nb095AlphaDummy336 u S_cls E)),
                                      ((nb095AlphaDummy293 D R S_cls E),
                                        (nb095AlphaDummy294 u S_cls f E)),
                                      ((nb095AlphaDummy291 D R S_cls E),
                                        (nb095AlphaDummy292 u S_cls f E)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0033`. -/
@[expose]
noncomputable def nb095SplitAlpha0033 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy377 D R S_cls E), (nb095AlphaDummy378 u S_cls)),
        ((nb095AlphaDummy346 D R S_cls E), (nb095AlphaDummy348 u S_cls)),
        ((nb095AlphaDummy345 D R S_cls E), (nb095AlphaDummy347 u S_cls)),
        ((nb095AlphaDummy375 D R S_cls E), (nb095AlphaDummy376 u S_cls)),
        ((nb095AlphaDummy349 D R S_cls E), (nb095AlphaDummy350 u S_cls)),
        ((nb095AlphaDummy340 D R S_cls E), (nb095AlphaDummy342 u S_cls)),
        ((nb095AlphaDummy339 D R S_cls E), (nb095AlphaDummy341 u S_cls)),
        ((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.classMem (Class.cv (nb095AlphaDummy377 D R S_cls E))
        (synCcompl (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))))
      (Wff.classMem (Class.cv (nb095AlphaDummy378 u S_cls))
        (synCcompl (synCphi (Class.cv (nb095AlphaDummy348 u S_cls))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095AlphaDummy346 D R S_cls E) ≠
                            (nb095AlphaDummy353 D R S_cls E) from (by
                            unfold nb095AlphaDummy353;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0358 D R S_cls E)
                                    0)))) (show (nb095AlphaDummy348 u S_cls) ≠
                            (nb095AlphaDummy355 u S_cls) from (by
                            unfold nb095AlphaDummy355;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0359 u S_cls) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy346 D R S_cls E) ≠
                              (nb095AlphaDummy354 D R S_cls E) from (by
                              unfold nb095AlphaDummy354;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0358 D R S_cls E)
                                      1)))) (show (nb095AlphaDummy348 u S_cls) ≠
                              (nb095AlphaDummy356 u S_cls) from (by
                              unfold nb095AlphaDummy356;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0359 u S_cls)
                                      1)))) (TAlphaVar.there (show
                              (nb095AlphaDummy346 D R S_cls E) ≠
                                (nb095AlphaDummy379 D R S_cls E) from (by
                                unfold nb095AlphaDummy379;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0388 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy348 u S_cls) ≠ (nb095AlphaDummy380 u S_cls)
                              from (by
                                unfold nb095AlphaDummy380;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0389 u S_cls)
                                        0)))) (TAlphaVar.there (show
                                (nb095AlphaDummy346 D R S_cls E) ≠
                                  (nb095AlphaDummy377 D R S_cls E) from (by
                                  unfold nb095AlphaDummy377;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0386 D R S_cls E) 0)))) (show
                                (nb095AlphaDummy348 u S_cls) ≠
                                  (nb095AlphaDummy378 u S_cls) from (by
                                  unfold nb095AlphaDummy378;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0387 u S_cls)
                                          0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                    (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb095AlphaDummy346 D R S_cls E))).fv) (by decide))
                        (freshVar_injective
                          (((Class.cv (nb095AlphaDummy348 u S_cls))).fv) (by decide))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095AlphaDummy353 D R S_cls E) ≠ (nb095AlphaDummy360 D R S_cls E) from (by
          unfold nb095AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0362 D R S_cls E)
                  1)))) (show (nb095AlphaDummy355 u S_cls) ≠ (nb095AlphaDummy363 u S_cls)
        from (by
          unfold nb095AlphaDummy363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0363 u S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy353 D R S_cls E) ≠
        (nb095AlphaDummy359 D R S_cls E) from (by
          unfold nb095AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0362 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy355 u S_cls) ≠ (nb095AlphaDummy362 u S_cls)
        from (by
          unfold nb095AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0363 u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy353 D R S_cls E) ≠
        (nb095AlphaDummy357 D R S_cls E) from (by
          unfold nb095AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0360 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy355 u S_cls) ≠ (nb095AlphaDummy358 u S_cls)
        from (by
          unfold nb095AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0361 u S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy361 D R S_cls E), (nb095AlphaDummy364 u S_cls)),
        ((nb095AlphaDummy360 D R S_cls E), (nb095AlphaDummy363 u S_cls)),
        ((nb095AlphaDummy359 D R S_cls E), (nb095AlphaDummy362 u S_cls)),
        ((nb095AlphaDummy357 D R S_cls E), (nb095AlphaDummy358 u S_cls)),
        ((nb095AlphaDummy353 D R S_cls E), (nb095AlphaDummy355 u S_cls)),
        ((nb095AlphaDummy354 D R S_cls E), (nb095AlphaDummy356 u S_cls)),
        ((nb095AlphaDummy379 D R S_cls E), (nb095AlphaDummy380 u S_cls)),
        ((nb095AlphaDummy377 D R S_cls E), (nb095AlphaDummy378 u S_cls)),
        ((nb095AlphaDummy346 D R S_cls E), (nb095AlphaDummy348 u S_cls)),
        ((nb095AlphaDummy345 D R S_cls E), (nb095AlphaDummy347 u S_cls)),
        ((nb095AlphaDummy375 D R S_cls E), (nb095AlphaDummy376 u S_cls)),
        ((nb095AlphaDummy349 D R S_cls E), (nb095AlphaDummy350 u S_cls)),
        ((nb095AlphaDummy340 D R S_cls E), (nb095AlphaDummy342 u S_cls)),
        ((nb095AlphaDummy339 D R S_cls E), (nb095AlphaDummy341 u S_cls)),
        ((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
                                        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠ (nb095AlphaDummy367
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0366
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy368 u S_cls)
        from (by
          unfold
            nb095AlphaDummy368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0367
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠
        (nb095AlphaDummy365 D R S_cls E) from (by
          unfold
            nb095AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0364
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy366 u S_cls)
        from (by
          unfold
            nb095AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0365
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy353
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠ (nb095AlphaDummy367
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0370
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy368 u S_cls)
        from (by
          unfold
            nb095AlphaDummy368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0371
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠
        (nb095AlphaDummy365 D R S_cls E) from (by
          unfold
            nb095AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0368
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy366 u S_cls)
        from (by
          unfold
            nb095AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0369
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠ (nb095AlphaDummy367
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0366
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy368 u S_cls)
        from (by
          unfold
            nb095AlphaDummy368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0367
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠
        (nb095AlphaDummy365 D R S_cls E) from (by
          unfold
            nb095AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0364
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy366 u S_cls)
        from (by
          unfold
            nb095AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0365
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy353
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠ (nb095AlphaDummy367
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0370
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy368 u S_cls)
        from (by
          unfold
            nb095AlphaDummy368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0371
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠
        (nb095AlphaDummy365 D R S_cls E) from (by
          unfold
            nb095AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0368
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy366 u S_cls)
        from (by
          unfold
            nb095AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0369
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy361 D R S_cls E), (nb095AlphaDummy364 u S_cls)),
        ((nb095AlphaDummy360 D R S_cls E), (nb095AlphaDummy363 u S_cls)),
        ((nb095AlphaDummy359 D R S_cls E), (nb095AlphaDummy362 u S_cls)),
        ((nb095AlphaDummy357 D R S_cls E), (nb095AlphaDummy358 u S_cls)),
        ((nb095AlphaDummy353 D R S_cls E), (nb095AlphaDummy355 u S_cls)),
        ((nb095AlphaDummy354 D R S_cls E), (nb095AlphaDummy356 u S_cls)),
        ((nb095AlphaDummy379 D R S_cls E), (nb095AlphaDummy380 u S_cls)),
        ((nb095AlphaDummy377 D R S_cls E), (nb095AlphaDummy378 u S_cls)),
        ((nb095AlphaDummy346 D R S_cls E), (nb095AlphaDummy348 u S_cls)),
        ((nb095AlphaDummy345 D R S_cls E), (nb095AlphaDummy347 u S_cls)),
        ((nb095AlphaDummy375 D R S_cls E), (nb095AlphaDummy376 u S_cls)),
        ((nb095AlphaDummy349 D R S_cls E), (nb095AlphaDummy350 u S_cls)),
        ((nb095AlphaDummy340 D R S_cls E), (nb095AlphaDummy342 u S_cls)),
        ((nb095AlphaDummy339 D R S_cls E), (nb095AlphaDummy341 u S_cls)),
        ((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy353 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy353 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy360 D
        R S_cls E) ≠ (nb095AlphaDummy371 D R S_cls E) from (by
          unfold
            nb095AlphaDummy371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0374
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy372 u S_cls)
        from (by
          unfold
            nb095AlphaDummy372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0375
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠
        (nb095AlphaDummy369 D R S_cls E) from (by
          unfold
            nb095AlphaDummy369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0372
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy370 u S_cls)
        from (by
          unfold
            nb095AlphaDummy370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0373
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy353
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠ (nb095AlphaDummy371
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0374
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy372 u S_cls)
        from (by
          unfold
            nb095AlphaDummy372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0375
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠
        (nb095AlphaDummy369 D R S_cls E) from (by
          unfold
            nb095AlphaDummy369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0372
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy370 u S_cls)
        from (by
          unfold
            nb095AlphaDummy370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0373
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy353
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy361 D
        R S_cls E) ≠ (nb095AlphaDummy373 D R S_cls E) from (by
          unfold
            nb095AlphaDummy373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0378
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy374 u S_cls)
        from (by
          unfold
            nb095AlphaDummy374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0379
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠
        (nb095AlphaDummy369 D R S_cls E) from (by
          unfold
            nb095AlphaDummy369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0376
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy370 u S_cls)
        from (by
          unfold
            nb095AlphaDummy370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0377
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy361 D
        R S_cls E) ≠ (nb095AlphaDummy373 D R S_cls E) from (by
          unfold
            nb095AlphaDummy373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0378
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy374 u S_cls)
        from (by
          unfold
            nb095AlphaDummy374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0379
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠
        (nb095AlphaDummy369 D R S_cls E) from (by
          unfold
            nb095AlphaDummy369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0376
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy370 u S_cls)
        from (by
          unfold
            nb095AlphaDummy370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0377
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy353 D R S_cls E) ≠
                                      (nb095AlphaDummy357 D R S_cls E) from (by
                                      unfold nb095AlphaDummy357;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy355 u S_cls) ≠
                                      (nb095AlphaDummy358 u S_cls) from (by
                                      unfold nb095AlphaDummy358;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0361 u S_cls) 0))))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                [((nb095AlphaDummy357 D R S_cls E),
                                    (nb095AlphaDummy358 u S_cls)),
                                  ((nb095AlphaDummy353 D R S_cls E),
                                    (nb095AlphaDummy355 u S_cls)),
                                  ((nb095AlphaDummy354 D R S_cls E),
                                    (nb095AlphaDummy356 u S_cls)),
                                  ((nb095AlphaDummy379 D R S_cls E),
                                    (nb095AlphaDummy380 u S_cls)),
                                  ((nb095AlphaDummy377 D R S_cls E),
                                    (nb095AlphaDummy378 u S_cls)),
                                  ((nb095AlphaDummy346 D R S_cls E),
                                    (nb095AlphaDummy348 u S_cls)),
                                  ((nb095AlphaDummy345 D R S_cls E),
                                    (nb095AlphaDummy347 u S_cls)),
                                  ((nb095AlphaDummy375 D R S_cls E),
                                    (nb095AlphaDummy376 u S_cls)),
                                  ((nb095AlphaDummy349 D R S_cls E),
                                    (nb095AlphaDummy350 u S_cls)),
                                  ((nb095AlphaDummy340 D R S_cls E),
                                    (nb095AlphaDummy342 u S_cls)),
                                  ((nb095AlphaDummy339 D R S_cls E),
                                    (nb095AlphaDummy341 u S_cls)),
                                  ((nb095AlphaDummy337 D R S_cls E),
                                    (nb095AlphaDummy338 u S_cls E)),
                                  ((nb095AlphaDummy335 D R S_cls E),
                                    (nb095AlphaDummy336 u S_cls E)),
                                  ((nb095AlphaDummy293 D R S_cls E),
                                    (nb095AlphaDummy294 u S_cls f E)),
                                  ((nb095AlphaDummy291 D R S_cls E),
                                    (nb095AlphaDummy292 u S_cls f E)),
                                  ((nb095AlphaDummy001 D R S_cls E), u),
                                  ((nb095AlphaDummy002 D R S_cls E), x),
                                  ((nb095AlphaDummy000 D R S_cls E), f)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb095AlphaDummy353 D R S_cls E) ≠
                                    (nb095AlphaDummy357 D R S_cls E) from (by
                                    unfold nb095AlphaDummy357;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy355 u S_cls) ≠
                                    (nb095AlphaDummy358 u S_cls) from (by
                                    unfold nb095AlphaDummy358;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0361 u S_cls) 0))))
                                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy353 D R S_cls E) ≠
                                      (nb095AlphaDummy357 D R S_cls E) from (by
                                      unfold nb095AlphaDummy357;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy355 u S_cls) ≠
                                      (nb095AlphaDummy358 u S_cls) from (by
                                      unfold nb095AlphaDummy358;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0361 u S_cls) 0))))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                [((nb095AlphaDummy357 D R S_cls E),
                                    (nb095AlphaDummy358 u S_cls)),
                                  ((nb095AlphaDummy353 D R S_cls E),
                                    (nb095AlphaDummy355 u S_cls)),
                                  ((nb095AlphaDummy354 D R S_cls E),
                                    (nb095AlphaDummy356 u S_cls)),
                                  ((nb095AlphaDummy379 D R S_cls E),
                                    (nb095AlphaDummy380 u S_cls)),
                                  ((nb095AlphaDummy377 D R S_cls E),
                                    (nb095AlphaDummy378 u S_cls)),
                                  ((nb095AlphaDummy346 D R S_cls E),
                                    (nb095AlphaDummy348 u S_cls)),
                                  ((nb095AlphaDummy345 D R S_cls E),
                                    (nb095AlphaDummy347 u S_cls)),
                                  ((nb095AlphaDummy375 D R S_cls E),
                                    (nb095AlphaDummy376 u S_cls)),
                                  ((nb095AlphaDummy349 D R S_cls E),
                                    (nb095AlphaDummy350 u S_cls)),
                                  ((nb095AlphaDummy340 D R S_cls E),
                                    (nb095AlphaDummy342 u S_cls)),
                                  ((nb095AlphaDummy339 D R S_cls E),
                                    (nb095AlphaDummy341 u S_cls)),
                                  ((nb095AlphaDummy337 D R S_cls E),
                                    (nb095AlphaDummy338 u S_cls E)),
                                  ((nb095AlphaDummy335 D R S_cls E),
                                    (nb095AlphaDummy336 u S_cls E)),
                                  ((nb095AlphaDummy293 D R S_cls E),
                                    (nb095AlphaDummy294 u S_cls f E)),
                                  ((nb095AlphaDummy291 D R S_cls E),
                                    (nb095AlphaDummy292 u S_cls f E)),
                                  ((nb095AlphaDummy001 D R S_cls E), u),
                                  ((nb095AlphaDummy002 D R S_cls E), x),
                                  ((nb095AlphaDummy000 D R S_cls E), f)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095AlphaDummy346 D R S_cls E) ≠
                            (nb095AlphaDummy353 D R S_cls E) from (by
                            unfold nb095AlphaDummy353;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0358 D R S_cls E)
                                    0)))) (show (nb095AlphaDummy348 u S_cls) ≠
                            (nb095AlphaDummy355 u S_cls) from (by
                            unfold nb095AlphaDummy355;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0359 u S_cls) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy346 D R S_cls E) ≠
                              (nb095AlphaDummy354 D R S_cls E) from (by
                              unfold nb095AlphaDummy354;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0358 D R S_cls E)
                                      1)))) (show (nb095AlphaDummy348 u S_cls) ≠
                              (nb095AlphaDummy356 u S_cls) from (by
                              unfold nb095AlphaDummy356;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0359 u S_cls)
                                      1)))) (TAlphaVar.there (show
                              (nb095AlphaDummy346 D R S_cls E) ≠
                                (nb095AlphaDummy379 D R S_cls E) from (by
                                unfold nb095AlphaDummy379;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0388 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy348 u S_cls) ≠ (nb095AlphaDummy380 u S_cls)
                              from (by
                                unfold nb095AlphaDummy380;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0389 u S_cls)
                                        0)))) (TAlphaVar.there (show
                                (nb095AlphaDummy346 D R S_cls E) ≠
                                  (nb095AlphaDummy377 D R S_cls E) from (by
                                  unfold nb095AlphaDummy377;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0386 D R S_cls E) 0)))) (show
                                (nb095AlphaDummy348 u S_cls) ≠
                                  (nb095AlphaDummy378 u S_cls) from (by
                                  unfold nb095AlphaDummy378;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0387 u S_cls)
                                          0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                    (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb095AlphaDummy346 D R S_cls E))).fv) (by decide))
                        (freshVar_injective
                          (((Class.cv (nb095AlphaDummy348 u S_cls))).fv) (by decide))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095AlphaDummy353 D R S_cls E) ≠ (nb095AlphaDummy360 D R S_cls E) from (by
          unfold nb095AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0362 D R S_cls E)
                  1)))) (show (nb095AlphaDummy355 u S_cls) ≠ (nb095AlphaDummy363 u S_cls)
        from (by
          unfold nb095AlphaDummy363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0363 u S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy353 D R S_cls E) ≠
        (nb095AlphaDummy359 D R S_cls E) from (by
          unfold nb095AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0362 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy355 u S_cls) ≠ (nb095AlphaDummy362 u S_cls)
        from (by
          unfold nb095AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0363 u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy353 D R S_cls E) ≠
        (nb095AlphaDummy357 D R S_cls E) from (by
          unfold nb095AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0360 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy355 u S_cls) ≠ (nb095AlphaDummy358 u S_cls)
        from (by
          unfold nb095AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0361 u S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy361 D R S_cls E), (nb095AlphaDummy364 u S_cls)),
        ((nb095AlphaDummy360 D R S_cls E), (nb095AlphaDummy363 u S_cls)),
        ((nb095AlphaDummy359 D R S_cls E), (nb095AlphaDummy362 u S_cls)),
        ((nb095AlphaDummy357 D R S_cls E), (nb095AlphaDummy358 u S_cls)),
        ((nb095AlphaDummy353 D R S_cls E), (nb095AlphaDummy355 u S_cls)),
        ((nb095AlphaDummy354 D R S_cls E), (nb095AlphaDummy356 u S_cls)),
        ((nb095AlphaDummy379 D R S_cls E), (nb095AlphaDummy380 u S_cls)),
        ((nb095AlphaDummy377 D R S_cls E), (nb095AlphaDummy378 u S_cls)),
        ((nb095AlphaDummy346 D R S_cls E), (nb095AlphaDummy348 u S_cls)),
        ((nb095AlphaDummy345 D R S_cls E), (nb095AlphaDummy347 u S_cls)),
        ((nb095AlphaDummy375 D R S_cls E), (nb095AlphaDummy376 u S_cls)),
        ((nb095AlphaDummy349 D R S_cls E), (nb095AlphaDummy350 u S_cls)),
        ((nb095AlphaDummy340 D R S_cls E), (nb095AlphaDummy342 u S_cls)),
        ((nb095AlphaDummy339 D R S_cls E), (nb095AlphaDummy341 u S_cls)),
        ((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
                                        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠ (nb095AlphaDummy367
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0366
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy368 u S_cls)
        from (by
          unfold
            nb095AlphaDummy368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0367
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠
        (nb095AlphaDummy365 D R S_cls E) from (by
          unfold
            nb095AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0364
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy366 u S_cls)
        from (by
          unfold
            nb095AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0365
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy353
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠ (nb095AlphaDummy367
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0370
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy368 u S_cls)
        from (by
          unfold
            nb095AlphaDummy368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0371
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠
        (nb095AlphaDummy365 D R S_cls E) from (by
          unfold
            nb095AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0368
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy366 u S_cls)
        from (by
          unfold
            nb095AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0369
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠ (nb095AlphaDummy367
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0366
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy368 u S_cls)
        from (by
          unfold
            nb095AlphaDummy368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0367
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠
        (nb095AlphaDummy365 D R S_cls E) from (by
          unfold
            nb095AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0364
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy366 u S_cls)
        from (by
          unfold
            nb095AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0365
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy353
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠ (nb095AlphaDummy367
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0370
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy368 u S_cls)
        from (by
          unfold
            nb095AlphaDummy368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0371
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠
        (nb095AlphaDummy365 D R S_cls E) from (by
          unfold
            nb095AlphaDummy365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0368
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy366 u S_cls)
        from (by
          unfold
            nb095AlphaDummy366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0369
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy361 D R S_cls E), (nb095AlphaDummy364 u S_cls)),
        ((nb095AlphaDummy360 D R S_cls E), (nb095AlphaDummy363 u S_cls)),
        ((nb095AlphaDummy359 D R S_cls E), (nb095AlphaDummy362 u S_cls)),
        ((nb095AlphaDummy357 D R S_cls E), (nb095AlphaDummy358 u S_cls)),
        ((nb095AlphaDummy353 D R S_cls E), (nb095AlphaDummy355 u S_cls)),
        ((nb095AlphaDummy354 D R S_cls E), (nb095AlphaDummy356 u S_cls)),
        ((nb095AlphaDummy379 D R S_cls E), (nb095AlphaDummy380 u S_cls)),
        ((nb095AlphaDummy377 D R S_cls E), (nb095AlphaDummy378 u S_cls)),
        ((nb095AlphaDummy346 D R S_cls E), (nb095AlphaDummy348 u S_cls)),
        ((nb095AlphaDummy345 D R S_cls E), (nb095AlphaDummy347 u S_cls)),
        ((nb095AlphaDummy375 D R S_cls E), (nb095AlphaDummy376 u S_cls)),
        ((nb095AlphaDummy349 D R S_cls E), (nb095AlphaDummy350 u S_cls)),
        ((nb095AlphaDummy340 D R S_cls E), (nb095AlphaDummy342 u S_cls)),
        ((nb095AlphaDummy339 D R S_cls E), (nb095AlphaDummy341 u S_cls)),
        ((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy353 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy353 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy360 D
        R S_cls E) ≠ (nb095AlphaDummy371 D R S_cls E) from (by
          unfold
            nb095AlphaDummy371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0374
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy372 u S_cls)
        from (by
          unfold
            nb095AlphaDummy372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0375
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠
        (nb095AlphaDummy369 D R S_cls E) from (by
          unfold
            nb095AlphaDummy369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0372
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy370 u S_cls)
        from (by
          unfold
            nb095AlphaDummy370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0373
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy353
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠ (nb095AlphaDummy371
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0374
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy372 u S_cls)
        from (by
          unfold
            nb095AlphaDummy372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0375
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy360 D R S_cls E) ≠
        (nb095AlphaDummy369 D R S_cls E) from (by
          unfold
            nb095AlphaDummy369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0372
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy370 u S_cls)
        from (by
          unfold
            nb095AlphaDummy370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0373
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy353
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy361 D
        R S_cls E) ≠ (nb095AlphaDummy373 D R S_cls E) from (by
          unfold
            nb095AlphaDummy373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0378
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy374 u S_cls)
        from (by
          unfold
            nb095AlphaDummy374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0379
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠
        (nb095AlphaDummy369 D R S_cls E) from (by
          unfold
            nb095AlphaDummy369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0376
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy370 u S_cls)
        from (by
          unfold
            nb095AlphaDummy370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0377
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy361 D
        R S_cls E) ≠ (nb095AlphaDummy373 D R S_cls E) from (by
          unfold
            nb095AlphaDummy373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0378
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy374 u S_cls)
        from (by
          unfold
            nb095AlphaDummy374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0379
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy361 D R S_cls E) ≠
        (nb095AlphaDummy369 D R S_cls E) from (by
          unfold
            nb095AlphaDummy369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0376
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy364 u S_cls) ≠ (nb095AlphaDummy370 u S_cls)
        from (by
          unfold
            nb095AlphaDummy370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0377
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy353 D R S_cls E) ≠
                                      (nb095AlphaDummy357 D R S_cls E) from (by
                                      unfold nb095AlphaDummy357;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy355 u S_cls) ≠
                                      (nb095AlphaDummy358 u S_cls) from (by
                                      unfold nb095AlphaDummy358;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0361 u S_cls) 0))))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                [((nb095AlphaDummy357 D R S_cls E),
                                    (nb095AlphaDummy358 u S_cls)),
                                  ((nb095AlphaDummy353 D R S_cls E),
                                    (nb095AlphaDummy355 u S_cls)),
                                  ((nb095AlphaDummy354 D R S_cls E),
                                    (nb095AlphaDummy356 u S_cls)),
                                  ((nb095AlphaDummy379 D R S_cls E),
                                    (nb095AlphaDummy380 u S_cls)),
                                  ((nb095AlphaDummy377 D R S_cls E),
                                    (nb095AlphaDummy378 u S_cls)),
                                  ((nb095AlphaDummy346 D R S_cls E),
                                    (nb095AlphaDummy348 u S_cls)),
                                  ((nb095AlphaDummy345 D R S_cls E),
                                    (nb095AlphaDummy347 u S_cls)),
                                  ((nb095AlphaDummy375 D R S_cls E),
                                    (nb095AlphaDummy376 u S_cls)),
                                  ((nb095AlphaDummy349 D R S_cls E),
                                    (nb095AlphaDummy350 u S_cls)),
                                  ((nb095AlphaDummy340 D R S_cls E),
                                    (nb095AlphaDummy342 u S_cls)),
                                  ((nb095AlphaDummy339 D R S_cls E),
                                    (nb095AlphaDummy341 u S_cls)),
                                  ((nb095AlphaDummy337 D R S_cls E),
                                    (nb095AlphaDummy338 u S_cls E)),
                                  ((nb095AlphaDummy335 D R S_cls E),
                                    (nb095AlphaDummy336 u S_cls E)),
                                  ((nb095AlphaDummy293 D R S_cls E),
                                    (nb095AlphaDummy294 u S_cls f E)),
                                  ((nb095AlphaDummy291 D R S_cls E),
                                    (nb095AlphaDummy292 u S_cls f E)),
                                  ((nb095AlphaDummy001 D R S_cls E), u),
                                  ((nb095AlphaDummy002 D R S_cls E), x),
                                  ((nb095AlphaDummy000 D R S_cls E), f)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb095AlphaDummy353 D R S_cls E) ≠
                                    (nb095AlphaDummy357 D R S_cls E) from (by
                                    unfold nb095AlphaDummy357;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy355 u S_cls) ≠
                                    (nb095AlphaDummy358 u S_cls) from (by
                                    unfold nb095AlphaDummy358;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0361 u S_cls) 0))))
                                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy353 D R S_cls E) ≠
                                      (nb095AlphaDummy357 D R S_cls E) from (by
                                      unfold nb095AlphaDummy357;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy355 u S_cls) ≠
                                      (nb095AlphaDummy358 u S_cls) from (by
                                      unfold nb095AlphaDummy358;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0361 u S_cls) 0))))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                [((nb095AlphaDummy357 D R S_cls E),
                                    (nb095AlphaDummy358 u S_cls)),
                                  ((nb095AlphaDummy353 D R S_cls E),
                                    (nb095AlphaDummy355 u S_cls)),
                                  ((nb095AlphaDummy354 D R S_cls E),
                                    (nb095AlphaDummy356 u S_cls)),
                                  ((nb095AlphaDummy379 D R S_cls E),
                                    (nb095AlphaDummy380 u S_cls)),
                                  ((nb095AlphaDummy377 D R S_cls E),
                                    (nb095AlphaDummy378 u S_cls)),
                                  ((nb095AlphaDummy346 D R S_cls E),
                                    (nb095AlphaDummy348 u S_cls)),
                                  ((nb095AlphaDummy345 D R S_cls E),
                                    (nb095AlphaDummy347 u S_cls)),
                                  ((nb095AlphaDummy375 D R S_cls E),
                                    (nb095AlphaDummy376 u S_cls)),
                                  ((nb095AlphaDummy349 D R S_cls E),
                                    (nb095AlphaDummy350 u S_cls)),
                                  ((nb095AlphaDummy340 D R S_cls E),
                                    (nb095AlphaDummy342 u S_cls)),
                                  ((nb095AlphaDummy339 D R S_cls E),
                                    (nb095AlphaDummy341 u S_cls)),
                                  ((nb095AlphaDummy337 D R S_cls E),
                                    (nb095AlphaDummy338 u S_cls E)),
                                  ((nb095AlphaDummy335 D R S_cls E),
                                    (nb095AlphaDummy336 u S_cls E)),
                                  ((nb095AlphaDummy293 D R S_cls E),
                                    (nb095AlphaDummy294 u S_cls f E)),
                                  ((nb095AlphaDummy291 D R S_cls E),
                                    (nb095AlphaDummy292 u S_cls f E)),
                                  ((nb095AlphaDummy001 D R S_cls E), u),
                                  ((nb095AlphaDummy002 D R S_cls E), x),
                                  ((nb095AlphaDummy000 D R S_cls E), f)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))

theorem nb095_focused_notmem_0029 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy340 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((synCcnv (synCdif S_cls (synCid)))).fv ∪
          ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv)
        1 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif S_cls (synCid))]
  rw [fv_syn_cdif S_cls (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0988 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy340 D R S_cls E) ∉ ((synCcnv (synCdif S_cls (synCid)))).fv := by
  simpa only [nb095AlphaDummy340, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0029 D R S_cls E)
      (nb095_compact_fv_empty_0272 D R S_cls E))

theorem nb095_focused_notmem_0030 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy342 u S_cls) ∉ S_cls.fv :=
  by
  change
    freshVar (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn (Class.cv u))).fv)
        1 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif S_cls (synCid))]
  rw [fv_syn_cdif S_cls (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0989 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy342 u S_cls) ∉ ((synCcnv (synCdif S_cls (synCid)))).fv := by
  simpa only [nb095AlphaDummy342, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0030 u S_cls) (nb095_compact_fv_empty_0273 u S_cls))

theorem nb095_focused_notmem_0031 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy339 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((synCcnv (synCdif S_cls (synCid)))).fv ∪
          ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif S_cls (synCid))]
  rw [fv_syn_cdif S_cls (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0990 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy339 D R S_cls E) ∉ ((synCcnv (synCdif S_cls (synCid)))).fv := by
  simpa only [nb095AlphaDummy339, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0031 D R S_cls E)
      (nb095_compact_fv_empty_0274 D R S_cls E))

theorem nb095_focused_notmem_0032 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy341 u S_cls) ∉ S_cls.fv :=
  by
  change
    freshVar (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn (Class.cv u))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif S_cls (synCid))]
  rw [fv_syn_cdif S_cls (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0991 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy341 u S_cls) ∉ ((synCcnv (synCdif S_cls (synCid)))).fv := by
  simpa only [nb095AlphaDummy341, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0032 u S_cls) (nb095_compact_fv_empty_0275 u S_cls))

theorem nb095_focused_notmem_0033 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy337 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        ((E).fv ∪ ((synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif S_cls (synCid)))
      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif S_cls (synCid))]
  rw [fv_syn_cdif S_cls (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0992 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy337 D R S_cls E) ∉ ((synCcnv (synCdif S_cls (synCid)))).fv := by
  simpa only [nb095AlphaDummy337, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0033 D R S_cls E)
      (nb095_compact_fv_empty_0276 D R S_cls E))

theorem nb095_focused_notmem_0034 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy338 u S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        ((E).fv ∪ ((synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif S_cls (synCid))]
  rw [fv_syn_cdif S_cls (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0993 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy338 u S_cls E) ∉ ((synCcnv (synCdif S_cls (synCid)))).fv := by
  simpa only [nb095AlphaDummy338, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0034 u S_cls E) (nb095_compact_fv_empty_0277 u S_cls E))

theorem nb095_focused_notmem_0035 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy335 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((synCnin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv ∪ ((synCnin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin E
      (synCima (synCcnv (synCdif S_cls (synCid)))
        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif S_cls (synCid)))
      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif S_cls (synCid))]
  rw [fv_syn_cdif S_cls (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0994 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy335 D R S_cls E) ∉ ((synCcnv (synCdif S_cls (synCid)))).fv := by
  simpa only [nb095AlphaDummy335, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0035 D R S_cls E)
      (nb095_compact_fv_empty_0278 D R S_cls E))

theorem nb095_focused_notmem_0036 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy336 u S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((synCnin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv u))))).fv ∪ ((synCnin E
              (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin E
      (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif S_cls (synCid))]
  rw [fv_syn_cdif S_cls (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0995 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy336 u S_cls E) ∉ ((synCcnv (synCdif S_cls (synCid)))).fv := by
  simpa only [nb095AlphaDummy336, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0036 u S_cls E) (nb095_compact_fv_empty_0279 u S_cls E))

theorem nb095_focused_notmem_0037 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy293 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((synCrn (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪ ((synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid)))
        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif S_cls (synCid)))
      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif S_cls (synCid))]
  rw [fv_syn_cdif S_cls (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0996 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy293 D R S_cls E) ∉ ((synCcnv (synCdif S_cls (synCid)))).fv := by
  simpa only [nb095AlphaDummy293, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0037 D R S_cls E)
      (nb095_compact_fv_empty_0222 D R S_cls E))

theorem nb095_focused_notmem_0038 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    (nb095AlphaDummy294 u S_cls f E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((synCrn (Class.cv f))).fv ∪ ((synCin E
              (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif S_cls (synCid))]
  rw [fv_syn_cdif S_cls (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0997 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    (nb095AlphaDummy294 u S_cls f E) ∉ ((synCcnv (synCdif S_cls (synCid)))).fv := by
  simpa only [nb095AlphaDummy294, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0038 u S_cls f E)
      (nb095_compact_fv_empty_0223 u S_cls f E))

theorem nb095_focused_notmem_0039 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy291 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((synCnin (synCrn (Class.cv (nb095AlphaDummy000 D R S_cls E))) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))).fv ∪
          ((synCnin (synCrn (Class.cv (nb095AlphaDummy000 D R S_cls E))) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin (synCrn (Class.cv (nb095AlphaDummy000 D R S_cls E)))
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
          (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid)))
        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif S_cls (synCid)))
      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif S_cls (synCid))]
  rw [fv_syn_cdif S_cls (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0998 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy291 D R S_cls E) ∉ ((synCcnv (synCdif S_cls (synCid)))).fv := by
  simpa only [nb095AlphaDummy291, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0039 D R S_cls E)
      (nb095_compact_fv_empty_0224 D R S_cls E))

theorem nb095_focused_notmem_0040 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    (nb095AlphaDummy292 u S_cls f E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((synCnin (synCrn (Class.cv f)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))).fv ∪
          ((synCnin (synCrn (Class.cv f)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin (synCrn (Class.cv f))
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif S_cls (synCid))]
  rw [fv_syn_cdif S_cls (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0999 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    (nb095AlphaDummy292 u S_cls f E) ∉ ((synCcnv (synCdif S_cls (synCid)))).fv := by
  simpa only [nb095AlphaDummy292, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0040 u S_cls f E)
      (nb095_compact_fv_empty_0225 u S_cls f E))

theorem nb095_focused_notmem_0041 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy001 D R S_cls E) ∉ S_cls.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 1 ∉ S_cls.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb095_wpp_notmem_1000 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy001 D R S_cls E) ∉ ((synCcnv (synCdif S_cls (synCid)))).fv := by
  simpa only [nb095AlphaDummy001, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0041 D R S_cls E)
      (nb095_compact_fv_empty_0030 D R S_cls E))

theorem nb095_wpp_notmem_1001 (u : Var) (S_cls : Class) (dv_S_u : u ∉ S_cls.fv) :
    u ∉ ((synCcnv (synCdif S_cls (synCid)))).fv := by
  simpa only [fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using
    (And.intro dv_S_u (nb095_compact_fv_empty_0031 u))

theorem nb095_focused_notmem_0042 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy002 D R S_cls E) ∉ S_cls.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 2 ∉ S_cls.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb095_wpp_notmem_1002 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy002 D R S_cls E) ∉ ((synCcnv (synCdif S_cls (synCid)))).fv := by
  simpa only [nb095AlphaDummy002, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0042 D R S_cls E)
      (nb095_compact_fv_empty_0032 D R S_cls E))

theorem nb095_wpp_notmem_1003 (x : Var) (S_cls : Class) (dv_S_x : x ∉ S_cls.fv) :
    x ∉ ((synCcnv (synCdif S_cls (synCid)))).fv := by
  simpa only [fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using
    (And.intro dv_S_x (nb095_compact_fv_empty_0033 x))

theorem nb095_focused_notmem_0043 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy000 D R S_cls E) ∉ S_cls.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 0 ∉ S_cls.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb095_wpp_notmem_1004 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy000 D R S_cls E) ∉ ((synCcnv (synCdif S_cls (synCid)))).fv := by
  simpa only [nb095AlphaDummy000, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0043 D R S_cls E)
      (nb095_compact_fv_empty_0034 D R S_cls E))

theorem nb095_wpp_notmem_1005 (S_cls : Class) (f : Var) (dv_S_f : f ∉ S_cls.fv) :
    f ∉ ((synCcnv (synCdif S_cls (synCid)))).fv := by
  simpa only [fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using
    (And.intro dv_S_f (nb095_compact_fv_empty_0035 f))

theorem nb095_compact_envfresh_0120 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_S_f : f ∉ S_cls.fv) (dv_S_u : u ∉ S_cls.fv)
    (dv_S_x : x ∉ S_cls.fv) :
    TEnvFresh
      [((nb095AlphaDummy340 D R S_cls E), (nb095AlphaDummy342 u S_cls)),
        ((nb095AlphaDummy339 D R S_cls E), (nb095AlphaDummy341 u S_cls)),
        ((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      ((synCcnv (synCdif S_cls (synCid)))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095AlphaDummy340 D R S_cls E)
      (nb095AlphaDummy342 u S_cls) (nb095_wpp_notmem_0988 D R S_cls E)
      (nb095_wpp_notmem_0989 u S_cls) (TEnvFresh.consFresh (nb095AlphaDummy339 D R S_cls E)
        (nb095AlphaDummy341 u S_cls) (nb095_wpp_notmem_0990 D R S_cls E)
        (nb095_wpp_notmem_0991 u S_cls) (TEnvFresh.consFresh (nb095AlphaDummy337 D R S_cls E)
          (nb095AlphaDummy338 u S_cls E) (nb095_wpp_notmem_0992 D R S_cls E)
          (nb095_wpp_notmem_0993 u S_cls E)
          (TEnvFresh.consFresh (nb095AlphaDummy335 D R S_cls E)
            (nb095AlphaDummy336 u S_cls E) (nb095_wpp_notmem_0994 D R S_cls E)
            (nb095_wpp_notmem_0995 u S_cls E)
            (TEnvFresh.consFresh (nb095AlphaDummy293 D R S_cls E)
              (nb095AlphaDummy294 u S_cls f E) (nb095_wpp_notmem_0996 D R S_cls E)
              (nb095_wpp_notmem_0997 u S_cls f E)
              (TEnvFresh.consFresh (nb095AlphaDummy291 D R S_cls E)
                (nb095AlphaDummy292 u S_cls f E) (nb095_wpp_notmem_0998 D R S_cls E)
                (nb095_wpp_notmem_0999 u S_cls f E)
                (TEnvFresh.consFresh (nb095AlphaDummy001 D R S_cls E) u
                  (nb095_wpp_notmem_1000 D R S_cls E) (nb095_wpp_notmem_1001 u S_cls dv_S_u)
                  (TEnvFresh.consFresh (nb095AlphaDummy002 D R S_cls E) x
                    (nb095_wpp_notmem_1002 D R S_cls E) (nb095_wpp_notmem_1003 x S_cls dv_S_x)
                    (TEnvFresh.consFresh (nb095AlphaDummy000 D R S_cls E) f
                      (nb095_wpp_notmem_1004 D R S_cls E) (nb095_wpp_notmem_1005 S_cls f dv_S_f)
                      (TEnvFresh.nil ((synCcnv (synCdif S_cls (synCid)))).fv))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
