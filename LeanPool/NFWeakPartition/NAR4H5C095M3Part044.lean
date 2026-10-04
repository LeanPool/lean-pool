/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C095M3Part044Stage1


/-! NF weak partition development: NAR4H5C095M3Part044. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_focused_refl_0010`. -/
@[expose]
noncomputable def nb095FocusedRefl0010 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_E_f : f ∉ E.fv) (dv_E_u : u ∉ E.fv)
    (dv_E_x : x ∉ E.fv) :
    TReflOn
      [((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy794 D R S_cls E), (nb095AlphaDummy796 u S_cls E)),
        ((nb095AlphaDummy793 D R S_cls E), (nb095AlphaDummy795 u S_cls E)),
        ((nb095AlphaDummy797 D R S_cls E), (nb095AlphaDummy798 u S_cls E)),
        ((nb095AlphaDummy791 D R S_cls E), (nb095AlphaDummy792 u S_cls E)),
        ((nb095AlphaDummy789 D R S_cls E), (nb095AlphaDummy790 u S_cls E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      E.fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0336 x u D R S_cls f E dv_E_f dv_E_u dv_E_x)

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0098`. -/
@[expose]
noncomputable def nb095SplitAlpha0098 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy351 D R S_cls E), (nb095AlphaDummy352 u S_cls)),
        ((nb095AlphaDummy349 D R S_cls E), (nb095AlphaDummy350 u S_cls)),
        ((nb095AlphaDummy340 D R S_cls E), (nb095AlphaDummy342 u S_cls)),
        ((nb095AlphaDummy339 D R S_cls E), (nb095AlphaDummy341 u S_cls)),
        ((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy794 D R S_cls E), (nb095AlphaDummy796 u S_cls E)),
        ((nb095AlphaDummy793 D R S_cls E), (nb095AlphaDummy795 u S_cls E)),
        ((nb095AlphaDummy797 D R S_cls E), (nb095AlphaDummy798 u S_cls E)),
        ((nb095AlphaDummy791 D R S_cls E), (nb095AlphaDummy792 u S_cls E)),
        ((nb095AlphaDummy789 D R S_cls E), (nb095AlphaDummy790 u S_cls E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
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
        ((nb095AlphaDummy794 D R S_cls E), (nb095AlphaDummy796 u S_cls E)),
        ((nb095AlphaDummy793 D R S_cls E), (nb095AlphaDummy795 u S_cls E)),
        ((nb095AlphaDummy797 D R S_cls E), (nb095AlphaDummy798 u S_cls E)),
        ((nb095AlphaDummy791 D R S_cls E), (nb095AlphaDummy792 u S_cls E)),
        ((nb095AlphaDummy789 D R S_cls E), (nb095AlphaDummy790 u S_cls E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
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
        ((nb095AlphaDummy794 D R S_cls E), (nb095AlphaDummy796 u S_cls E)),
        ((nb095AlphaDummy793 D R S_cls E), (nb095AlphaDummy795 u S_cls E)),
        ((nb095AlphaDummy797 D R S_cls E), (nb095AlphaDummy798 u S_cls E)),
        ((nb095AlphaDummy791 D R S_cls E), (nb095AlphaDummy792 u S_cls E)),
        ((nb095AlphaDummy789 D R S_cls E), (nb095AlphaDummy790 u S_cls E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
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
                                    ((nb095AlphaDummy794 D R S_cls E),
                                      (nb095AlphaDummy796 u S_cls E)),
                                    ((nb095AlphaDummy793 D R S_cls E),
                                      (nb095AlphaDummy795 u S_cls E)),
                                    ((nb095AlphaDummy797 D R S_cls E),
                                      (nb095AlphaDummy798 u S_cls E)),
                                    ((nb095AlphaDummy791 D R S_cls E),
                                      (nb095AlphaDummy792 u S_cls E)),
                                    ((nb095AlphaDummy789 D R S_cls E),
                                      (nb095AlphaDummy790 u S_cls E)),
                                    ((nb095AlphaDummy004 D R S_cls E),
                                      (nb095AlphaDummy006 x u D R S_cls f E)),
                                    ((nb095AlphaDummy003 D R S_cls E),
                                      (nb095AlphaDummy005 x u D R S_cls f E)),
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
                                    ((nb095AlphaDummy794 D R S_cls E),
                                      (nb095AlphaDummy796 u S_cls E)),
                                    ((nb095AlphaDummy793 D R S_cls E),
                                      (nb095AlphaDummy795 u S_cls E)),
                                    ((nb095AlphaDummy797 D R S_cls E),
                                      (nb095AlphaDummy798 u S_cls E)),
                                    ((nb095AlphaDummy791 D R S_cls E),
                                      (nb095AlphaDummy792 u S_cls E)),
                                    ((nb095AlphaDummy789 D R S_cls E),
                                      (nb095AlphaDummy790 u S_cls E)),
                                    ((nb095AlphaDummy004 D R S_cls E),
                                      (nb095AlphaDummy006 x u D R S_cls f E)),
                                    ((nb095AlphaDummy003 D R S_cls E),
                                      (nb095AlphaDummy005 x u D R S_cls f E)),
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
        ((nb095AlphaDummy794 D R S_cls E), (nb095AlphaDummy796 u S_cls E)),
        ((nb095AlphaDummy793 D R S_cls E), (nb095AlphaDummy795 u S_cls E)),
        ((nb095AlphaDummy797 D R S_cls E), (nb095AlphaDummy798 u S_cls E)),
        ((nb095AlphaDummy791 D R S_cls E), (nb095AlphaDummy792 u S_cls E)),
        ((nb095AlphaDummy789 D R S_cls E), (nb095AlphaDummy790 u S_cls E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
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
        ((nb095AlphaDummy794 D R S_cls E), (nb095AlphaDummy796 u S_cls E)),
        ((nb095AlphaDummy793 D R S_cls E), (nb095AlphaDummy795 u S_cls E)),
        ((nb095AlphaDummy797 D R S_cls E), (nb095AlphaDummy798 u S_cls E)),
        ((nb095AlphaDummy791 D R S_cls E), (nb095AlphaDummy792 u S_cls E)),
        ((nb095AlphaDummy789 D R S_cls E), (nb095AlphaDummy790 u S_cls E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
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
                                      ((nb095AlphaDummy794 D R S_cls E),
                                        (nb095AlphaDummy796 u S_cls E)),
                                      ((nb095AlphaDummy793 D R S_cls E),
                                        (nb095AlphaDummy795 u S_cls E)),
                                      ((nb095AlphaDummy797 D R S_cls E),
                                        (nb095AlphaDummy798 u S_cls E)),
                                      ((nb095AlphaDummy791 D R S_cls E),
                                        (nb095AlphaDummy792 u S_cls E)),
                                      ((nb095AlphaDummy789 D R S_cls E),
                                        (nb095AlphaDummy790 u S_cls E)),
                                      ((nb095AlphaDummy004 D R S_cls E),
                                        (nb095AlphaDummy006 x u D R S_cls f E)),
                                      ((nb095AlphaDummy003 D R S_cls E),
                                        (nb095AlphaDummy005 x u D R S_cls f E)),
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
                                      ((nb095AlphaDummy794 D R S_cls E),
                                        (nb095AlphaDummy796 u S_cls E)),
                                      ((nb095AlphaDummy793 D R S_cls E),
                                        (nb095AlphaDummy795 u S_cls E)),
                                      ((nb095AlphaDummy797 D R S_cls E),
                                        (nb095AlphaDummy798 u S_cls E)),
                                      ((nb095AlphaDummy791 D R S_cls E),
                                        (nb095AlphaDummy792 u S_cls E)),
                                      ((nb095AlphaDummy789 D R S_cls E),
                                        (nb095AlphaDummy790 u S_cls E)),
                                      ((nb095AlphaDummy004 D R S_cls E),
                                        (nb095AlphaDummy006 x u D R S_cls f E)),
                                      ((nb095AlphaDummy003 D R S_cls E),
                                        (nb095AlphaDummy005 x u D R S_cls f E)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
