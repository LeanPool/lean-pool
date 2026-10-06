/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C090C001Part060Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part060`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0038`. -/
@[expose]
noncomputable def nb090SplitAlpha0038 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy437 A), (nb090AlphaDummy438 h)),
        ((nb090AlphaDummy435 A), (nb090AlphaDummy436 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy437 A))
          (Class.cab (nb090AlphaDummy431 A)
            (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy423 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                (synCphi (Class.cv (nb090AlphaDummy432 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy437 A))
            (Class.cab (nb090AlphaDummy431 A)
              (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy423 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                  (synCphi (Class.cv (nb090AlphaDummy432 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy438 h))
          (Class.cab (nb090AlphaDummy433 h)
            (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy426 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                (synCphi (Class.cv (nb090AlphaDummy434 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy438 h))
            (Class.cab (nb090AlphaDummy433 h)
              (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy426 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                  (synCphi (Class.cv (nb090AlphaDummy434 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy432 A) from (by
                      unfold nb090AlphaDummy432;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0436 A) 1))))
                  (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy434 h) from (by
                      unfold nb090AlphaDummy434;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0438 h) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy431 A) from (by
                        unfold nb090AlphaDummy431;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0436 A) 0))))
                    (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy433 h) from (by
                        unfold nb090AlphaDummy433;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0438 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy437 A) from (by
                          unfold nb090AlphaDummy437;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0440 A) 0))))
                      (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy438 h) from (by
                          unfold nb090AlphaDummy438;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0441 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy435 A) from (by
                            unfold nb090AlphaDummy435;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0437 A) 0))))
                        (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy436 h) from (by
                            unfold nb090AlphaDummy436;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0439 h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪ ((synCcnv
                                  (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv)
                            (by decide)) (freshVar_injective (((synCcnv (Class.cv h))).fv ∪
                              ((synCcnv (synCcnv (Class.cv h)))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy423 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy424 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090AlphaDummy426 h))).fv ∪
                      ((Class.cv (nb090AlphaDummy427 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy432 A) ≠ (nb090AlphaDummy439 A) from (by
                              unfold nb090AlphaDummy439;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0442 A) 0))))
                          (show (nb090AlphaDummy434 h) ≠ (nb090AlphaDummy441 h) from (by
                              unfold nb090AlphaDummy441;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0443 h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy432 A) ≠ (nb090AlphaDummy440 A) from (by
                                unfold nb090AlphaDummy440;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0442 A) 1))))
                            (show (nb090AlphaDummy434 h) ≠ (nb090AlphaDummy442 h) from (by
                                unfold nb090AlphaDummy442;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0443 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy432 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy434 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy446 A) from (by
          unfold nb090AlphaDummy446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0446 A) 1)))) (show (nb090AlphaDummy441 h) ≠
        (nb090AlphaDummy449 h) from (by
          unfold nb090AlphaDummy449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0447 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy445 A) from (by
          unfold nb090AlphaDummy445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0446 A) 0)))) (show (nb090AlphaDummy441 h) ≠
        (nb090AlphaDummy448 h) from (by
          unfold nb090AlphaDummy448;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0447 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy443 A) from (by
          unfold nb090AlphaDummy443;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0444 A)
                  0)))) (show (nb090AlphaDummy441 h) ≠ (nb090AlphaDummy444 h) from (by
          unfold nb090AlphaDummy444;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0445 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy447 A), (nb090AlphaDummy450 h)), ((nb090AlphaDummy446 A),
        (nb090AlphaDummy449 h)), ((nb090AlphaDummy445 A), (nb090AlphaDummy448 h)),
        ((nb090AlphaDummy443 A), (nb090AlphaDummy444 h)), ((nb090AlphaDummy439 A),
        (nb090AlphaDummy441 h)), ((nb090AlphaDummy440 A), (nb090AlphaDummy442 h)),
        ((nb090AlphaDummy432 A), (nb090AlphaDummy434 h)), ((nb090AlphaDummy431 A),
        (nb090AlphaDummy433 h)), ((nb090AlphaDummy437 A), (nb090AlphaDummy438 h)),
        ((nb090AlphaDummy435 A), (nb090AlphaDummy436 h)), ((nb090AlphaDummy424 A),
        (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A),
        (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy446
        A) ≠ (nb090AlphaDummy453 A) from (by
          unfold
            nb090AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0450
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy454 h) from (by
          unfold
            nb090AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0451
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠
        (nb090AlphaDummy451 A) from (by
          unfold
            nb090AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0448
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy452 h) from (by
          unfold
            nb090AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0449
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy439
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠ (nb090AlphaDummy453 A) from (by
          unfold
            nb090AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0454
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy454 h) from (by
          unfold
            nb090AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0455
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠
        (nb090AlphaDummy451 A) from (by
          unfold
            nb090AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0452
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy452 h) from (by
          unfold
            nb090AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0453
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠ (nb090AlphaDummy453 A) from (by
          unfold
            nb090AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0450
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy454 h) from (by
          unfold
            nb090AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0451
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠
        (nb090AlphaDummy451 A) from (by
          unfold
            nb090AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0448
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy452 h) from (by
          unfold
            nb090AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0449
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy439
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠ (nb090AlphaDummy453 A) from (by
          unfold
            nb090AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0454
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy454 h) from (by
          unfold
            nb090AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0455
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠
        (nb090AlphaDummy451 A) from (by
          unfold
            nb090AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0452
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy452 h) from (by
          unfold
            nb090AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0453
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy447 A), (nb090AlphaDummy450 h)), ((nb090AlphaDummy446 A),
        (nb090AlphaDummy449 h)), ((nb090AlphaDummy445 A), (nb090AlphaDummy448 h)),
        ((nb090AlphaDummy443 A), (nb090AlphaDummy444 h)), ((nb090AlphaDummy439 A),
        (nb090AlphaDummy441 h)), ((nb090AlphaDummy440 A), (nb090AlphaDummy442 h)),
        ((nb090AlphaDummy432 A), (nb090AlphaDummy434 h)), ((nb090AlphaDummy431 A),
        (nb090AlphaDummy433 h)), ((nb090AlphaDummy437 A), (nb090AlphaDummy438 h)),
        ((nb090AlphaDummy435 A), (nb090AlphaDummy436 h)), ((nb090AlphaDummy424 A),
        (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A),
        (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy439 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy439 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy441
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠ (nb090AlphaDummy457 A) from (by
          unfold
            nb090AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0458
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy458 h) from (by
          unfold
            nb090AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0459
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠
        (nb090AlphaDummy455 A) from (by
          unfold
            nb090AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0456
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy456 h) from (by
          unfold
            nb090AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0457
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy439
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠ (nb090AlphaDummy457 A) from (by
          unfold
            nb090AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0458
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy458 h) from (by
          unfold
            nb090AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0459
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠
        (nb090AlphaDummy455 A) from (by
          unfold
            nb090AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0456
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy456 h) from (by
          unfold
            nb090AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0457
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy439
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy447
        A) ≠ (nb090AlphaDummy459 A) from (by
          unfold
            nb090AlphaDummy459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0462
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy460 h) from (by
          unfold
            nb090AlphaDummy460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0463
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠
        (nb090AlphaDummy455 A) from (by
          unfold
            nb090AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0460
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy456 h) from (by
          unfold
            nb090AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0461
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy447
        A) ≠ (nb090AlphaDummy459 A) from (by
          unfold
            nb090AlphaDummy459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0462
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy460 h) from (by
          unfold
            nb090AlphaDummy460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0463
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠
        (nb090AlphaDummy455 A) from (by
          unfold
            nb090AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0460
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy456 h) from (by
          unfold
            nb090AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0461
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy443 A) from
                                      (by
                                        unfold nb090AlphaDummy443;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0444 A)
                                                0)))) (show (nb090AlphaDummy441 h) ≠
                                        (nb090AlphaDummy444 h) from (by
                                        unfold nb090AlphaDummy444;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0445 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy443 A), (nb090AlphaDummy444 h)),
                                    ((nb090AlphaDummy439 A), (nb090AlphaDummy441 h)),
                                    ((nb090AlphaDummy440 A), (nb090AlphaDummy442 h)),
                                    ((nb090AlphaDummy432 A), (nb090AlphaDummy434 h)),
                                    ((nb090AlphaDummy431 A), (nb090AlphaDummy433 h)),
                                    ((nb090AlphaDummy437 A), (nb090AlphaDummy438 h)),
                                    ((nb090AlphaDummy435 A), (nb090AlphaDummy436 h)),
                                    ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                    ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                    ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                    ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                    ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy443 A) from
                                    (by
                                      unfold nb090AlphaDummy443;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0444 A)
                                              0)))) (show
                                    (nb090AlphaDummy441 h) ≠ (nb090AlphaDummy444 h) from
                                    (by
                                      unfold nb090AlphaDummy444;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0445 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy443 A) from
                                      (by
                                        unfold nb090AlphaDummy443;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0444 A)
                                                0)))) (show (nb090AlphaDummy441 h) ≠
                                        (nb090AlphaDummy444 h) from (by
                                        unfold nb090AlphaDummy444;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0445 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy443 A), (nb090AlphaDummy444 h)),
                                    ((nb090AlphaDummy439 A), (nb090AlphaDummy441 h)),
                                    ((nb090AlphaDummy440 A), (nb090AlphaDummy442 h)),
                                    ((nb090AlphaDummy432 A), (nb090AlphaDummy434 h)),
                                    ((nb090AlphaDummy431 A), (nb090AlphaDummy433 h)),
                                    ((nb090AlphaDummy437 A), (nb090AlphaDummy438 h)),
                                    ((nb090AlphaDummy435 A), (nb090AlphaDummy436 h)),
                                    ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                    ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                    ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                    ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                    ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy432 A) from (by
                        unfold nb090AlphaDummy432;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0436 A) 1))))
                    (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy434 h) from (by
                        unfold nb090AlphaDummy434;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0438 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy431 A) from (by
                          unfold nb090AlphaDummy431;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0436 A) 0))))
                      (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy433 h) from (by
                          unfold nb090AlphaDummy433;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0438 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy437 A) from (by
                            unfold nb090AlphaDummy437;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0440 A) 0))))
                        (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy438 h) from (by
                            unfold nb090AlphaDummy438;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0441 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy435 A) from (by
                              unfold nb090AlphaDummy435;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0437 A) 0))))
                          (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy436 h) from (by
                              unfold nb090AlphaDummy436;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0439 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪ ((synCcnv
                                    (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv)
                              (by decide)) (freshVar_injective (((synCcnv (Class.cv h))).fv ∪
                                ((synCcnv (synCcnv (Class.cv h)))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy423 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy424 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy426 h))).fv ∪
                        ((Class.cv (nb090AlphaDummy427 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy432 A) ≠ (nb090AlphaDummy439 A) from (by
                                unfold nb090AlphaDummy439;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0442 A) 0))))
                            (show (nb090AlphaDummy434 h) ≠ (nb090AlphaDummy441 h) from (by
                                unfold nb090AlphaDummy441;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0443 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy432 A) ≠ (nb090AlphaDummy440 A) from
                                (by
                                  unfold nb090AlphaDummy440;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0442 A) 1))))
                              (show (nb090AlphaDummy434 h) ≠ (nb090AlphaDummy442 h) from
                                (by
                                  unfold nb090AlphaDummy442;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0443 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy432 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy434 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy446 A) from (by
          unfold nb090AlphaDummy446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0446 A) 1)))) (show (nb090AlphaDummy441 h) ≠
        (nb090AlphaDummy449 h) from (by
          unfold nb090AlphaDummy449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0447 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy445 A) from (by
          unfold nb090AlphaDummy445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0446 A)
                  0)))) (show (nb090AlphaDummy441 h) ≠ (nb090AlphaDummy448 h) from (by
          unfold nb090AlphaDummy448;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0447 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy439 A) ≠
        (nb090AlphaDummy443 A) from (by
          unfold nb090AlphaDummy443;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0444 A)
                  0)))) (show (nb090AlphaDummy441 h) ≠ (nb090AlphaDummy444 h) from (by
          unfold nb090AlphaDummy444;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0445 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy447 A), (nb090AlphaDummy450 h)), ((nb090AlphaDummy446 A),
        (nb090AlphaDummy449 h)), ((nb090AlphaDummy445 A), (nb090AlphaDummy448 h)),
        ((nb090AlphaDummy443 A), (nb090AlphaDummy444 h)), ((nb090AlphaDummy439 A),
        (nb090AlphaDummy441 h)), ((nb090AlphaDummy440 A), (nb090AlphaDummy442 h)),
        ((nb090AlphaDummy432 A), (nb090AlphaDummy434 h)), ((nb090AlphaDummy431 A),
        (nb090AlphaDummy433 h)), ((nb090AlphaDummy437 A), (nb090AlphaDummy438 h)),
        ((nb090AlphaDummy435 A), (nb090AlphaDummy436 h)), ((nb090AlphaDummy424 A),
        (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A),
        (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy446
        A) ≠ (nb090AlphaDummy453 A) from (by
          unfold
            nb090AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0450
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy454 h) from (by
          unfold
            nb090AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0451
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠
        (nb090AlphaDummy451 A) from (by
          unfold
            nb090AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0448
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy452 h) from (by
          unfold
            nb090AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0449
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy439
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠ (nb090AlphaDummy453 A) from (by
          unfold
            nb090AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0454
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy454 h) from (by
          unfold
            nb090AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0455
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠
        (nb090AlphaDummy451 A) from (by
          unfold
            nb090AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0452
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy452 h) from (by
          unfold
            nb090AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0453
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠ (nb090AlphaDummy453 A) from (by
          unfold
            nb090AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0450
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy454 h) from (by
          unfold
            nb090AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0451
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠
        (nb090AlphaDummy451 A) from (by
          unfold
            nb090AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0448
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy452 h) from (by
          unfold
            nb090AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0449
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy439
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠ (nb090AlphaDummy453 A) from (by
          unfold
            nb090AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0454
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy454 h) from (by
          unfold
            nb090AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0455
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠
        (nb090AlphaDummy451 A) from (by
          unfold
            nb090AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0452
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy452 h) from (by
          unfold
            nb090AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0453
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy447 A), (nb090AlphaDummy450 h)), ((nb090AlphaDummy446 A),
        (nb090AlphaDummy449 h)), ((nb090AlphaDummy445 A), (nb090AlphaDummy448 h)),
        ((nb090AlphaDummy443 A), (nb090AlphaDummy444 h)), ((nb090AlphaDummy439 A),
        (nb090AlphaDummy441 h)), ((nb090AlphaDummy440 A), (nb090AlphaDummy442 h)),
        ((nb090AlphaDummy432 A), (nb090AlphaDummy434 h)), ((nb090AlphaDummy431 A),
        (nb090AlphaDummy433 h)), ((nb090AlphaDummy437 A), (nb090AlphaDummy438 h)),
        ((nb090AlphaDummy435 A), (nb090AlphaDummy436 h)), ((nb090AlphaDummy424 A),
        (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A),
        (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy439 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy439 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy441
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠ (nb090AlphaDummy457 A) from (by
          unfold
            nb090AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0458
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy458 h) from (by
          unfold
            nb090AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0459
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠
        (nb090AlphaDummy455 A) from (by
          unfold
            nb090AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0456
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy456 h) from (by
          unfold
            nb090AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0457
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy439
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠ (nb090AlphaDummy457 A) from (by
          unfold
            nb090AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0458
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy458 h) from (by
          unfold
            nb090AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0459
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠
        (nb090AlphaDummy455 A) from (by
          unfold
            nb090AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0456
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy456 h) from (by
          unfold
            nb090AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0457
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy439
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy447
        A) ≠ (nb090AlphaDummy459 A) from (by
          unfold
            nb090AlphaDummy459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0462
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy460 h) from (by
          unfold
            nb090AlphaDummy460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0463
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠
        (nb090AlphaDummy455 A) from (by
          unfold
            nb090AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0460
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy456 h) from (by
          unfold
            nb090AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0461
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy447
        A) ≠ (nb090AlphaDummy459 A) from (by
          unfold
            nb090AlphaDummy459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0462
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy460 h) from (by
          unfold
            nb090AlphaDummy460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0463
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠
        (nb090AlphaDummy455 A) from (by
          unfold
            nb090AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0460
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy456 h) from (by
          unfold
            nb090AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0461
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy443 A)
                                        from (by
                                          unfold nb090AlphaDummy443;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0444 A) 0)))) (show
                                        (nb090AlphaDummy441 h) ≠ (nb090AlphaDummy444 h)
                                        from (by
                                          unfold nb090AlphaDummy444;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0445 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy443 A), (nb090AlphaDummy444 h)),
                                      ((nb090AlphaDummy439 A), (nb090AlphaDummy441 h)),
                                      ((nb090AlphaDummy440 A), (nb090AlphaDummy442 h)),
                                      ((nb090AlphaDummy432 A), (nb090AlphaDummy434 h)),
                                      ((nb090AlphaDummy431 A), (nb090AlphaDummy433 h)),
                                      ((nb090AlphaDummy437 A), (nb090AlphaDummy438 h)),
                                      ((nb090AlphaDummy435 A), (nb090AlphaDummy436 h)),
                                      ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                      ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                      ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                      ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                      ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy443 A) from
                                      (by
                                        unfold nb090AlphaDummy443;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0444 A)
                                                0)))) (show (nb090AlphaDummy441 h) ≠
                                        (nb090AlphaDummy444 h) from (by
                                        unfold nb090AlphaDummy444;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0445 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy443 A)
                                        from (by
                                          unfold nb090AlphaDummy443;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0444 A) 0)))) (show
                                        (nb090AlphaDummy441 h) ≠ (nb090AlphaDummy444 h)
                                        from (by
                                          unfold nb090AlphaDummy444;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0445 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy443 A), (nb090AlphaDummy444 h)),
                                      ((nb090AlphaDummy439 A), (nb090AlphaDummy441 h)),
                                      ((nb090AlphaDummy440 A), (nb090AlphaDummy442 h)),
                                      ((nb090AlphaDummy432 A), (nb090AlphaDummy434 h)),
                                      ((nb090AlphaDummy431 A), (nb090AlphaDummy433 h)),
                                      ((nb090AlphaDummy437 A), (nb090AlphaDummy438 h)),
                                      ((nb090AlphaDummy435 A), (nb090AlphaDummy436 h)),
                                      ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                      ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                      ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                      ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                      ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part061`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0039`. -/
@[expose]
noncomputable def nb090SplitAlpha0039 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy463 A), (nb090AlphaDummy464 h)),
        ((nb090AlphaDummy432 A), (nb090AlphaDummy434 h)),
        ((nb090AlphaDummy431 A), (nb090AlphaDummy433 h)),
        ((nb090AlphaDummy461 A), (nb090AlphaDummy462 h)),
        ((nb090AlphaDummy435 A), (nb090AlphaDummy436 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.classMem (Class.cv (nb090AlphaDummy463 A))
        (synCcompl (synCphi (Class.cv (nb090AlphaDummy432 A)))))
      (Wff.classMem (Class.cv (nb090AlphaDummy464 h))
        (synCcompl (synCphi (Class.cv (nb090AlphaDummy434 h))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb090AlphaDummy432 A) ≠ (nb090AlphaDummy439 A) from (by
                            unfold nb090AlphaDummy439;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0442 A) 0))))
                        (show (nb090AlphaDummy434 h) ≠ (nb090AlphaDummy441 h) from (by
                            unfold nb090AlphaDummy441;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0443 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy432 A) ≠ (nb090AlphaDummy440 A) from (by
                              unfold nb090AlphaDummy440;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0442 A) 1))))
                          (show (nb090AlphaDummy434 h) ≠ (nb090AlphaDummy442 h) from (by
                              unfold nb090AlphaDummy442;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0443 h) 1))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy432 A) ≠ (nb090AlphaDummy465 A) from (by
                                unfold nb090AlphaDummy465;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0472 A) 0))))
                            (show (nb090AlphaDummy434 h) ≠ (nb090AlphaDummy466 h) from (by
                                unfold nb090AlphaDummy466;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0473 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy432 A) ≠ (nb090AlphaDummy463 A) from
                                (by
                                  unfold nb090AlphaDummy463;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0470 A) 0))))
                              (show (nb090AlphaDummy434 h) ≠ (nb090AlphaDummy464 h) from
                                (by
                                  unfold nb090AlphaDummy464;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0471 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb090AlphaDummy432 A))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb090AlphaDummy434 h))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090AlphaDummy439 A) ≠
        (nb090AlphaDummy446 A) from (by
          unfold nb090AlphaDummy446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0446 A) 1)))) (show (nb090AlphaDummy441 h) ≠
        (nb090AlphaDummy449 h) from (by
          unfold nb090AlphaDummy449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0447 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy445 A) from (by
          unfold nb090AlphaDummy445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0446 A) 0)))) (show (nb090AlphaDummy441 h) ≠
        (nb090AlphaDummy448 h) from (by
          unfold nb090AlphaDummy448;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0447 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy443 A) from (by
          unfold nb090AlphaDummy443;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0444 A) 0)))) (show (nb090AlphaDummy441 h) ≠
        (nb090AlphaDummy444 h) from (by
          unfold nb090AlphaDummy444;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0445 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy447 A), (nb090AlphaDummy450 h)), ((nb090AlphaDummy446 A),
        (nb090AlphaDummy449 h)), ((nb090AlphaDummy445 A), (nb090AlphaDummy448 h)),
        ((nb090AlphaDummy443 A), (nb090AlphaDummy444 h)), ((nb090AlphaDummy439 A),
        (nb090AlphaDummy441 h)), ((nb090AlphaDummy440 A), (nb090AlphaDummy442 h)),
        ((nb090AlphaDummy465 A), (nb090AlphaDummy466 h)), ((nb090AlphaDummy463 A),
        (nb090AlphaDummy464 h)), ((nb090AlphaDummy432 A), (nb090AlphaDummy434 h)),
        ((nb090AlphaDummy431 A), (nb090AlphaDummy433 h)), ((nb090AlphaDummy461 A),
        (nb090AlphaDummy462 h)), ((nb090AlphaDummy435 A), (nb090AlphaDummy436 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A),
        (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠ (nb090AlphaDummy453 A) from (by
          unfold
            nb090AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0450
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy454 h) from (by
          unfold
            nb090AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0451
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠
        (nb090AlphaDummy451 A) from (by
          unfold
            nb090AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0448
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy452 h) from (by
          unfold
            nb090AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0449
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy439
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠ (nb090AlphaDummy453 A) from (by
          unfold
            nb090AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0454
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy454 h) from (by
          unfold
            nb090AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0455
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠
        (nb090AlphaDummy451 A) from (by
          unfold
            nb090AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0452
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy452 h) from (by
          unfold
            nb090AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0453
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠ (nb090AlphaDummy453 A) from (by
          unfold
            nb090AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0450
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy454 h) from (by
          unfold
            nb090AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0451
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠
        (nb090AlphaDummy451 A) from (by
          unfold
            nb090AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0448
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy452 h) from (by
          unfold
            nb090AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0449
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy439
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠ (nb090AlphaDummy453 A) from (by
          unfold
            nb090AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0454
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy454 h) from (by
          unfold
            nb090AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0455
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠
        (nb090AlphaDummy451 A) from (by
          unfold
            nb090AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0452
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy452 h) from (by
          unfold
            nb090AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0453
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy447 A), (nb090AlphaDummy450 h)), ((nb090AlphaDummy446 A),
        (nb090AlphaDummy449 h)), ((nb090AlphaDummy445 A), (nb090AlphaDummy448 h)),
        ((nb090AlphaDummy443 A), (nb090AlphaDummy444 h)), ((nb090AlphaDummy439 A),
        (nb090AlphaDummy441 h)), ((nb090AlphaDummy440 A), (nb090AlphaDummy442 h)),
        ((nb090AlphaDummy465 A), (nb090AlphaDummy466 h)), ((nb090AlphaDummy463 A),
        (nb090AlphaDummy464 h)), ((nb090AlphaDummy432 A), (nb090AlphaDummy434 h)),
        ((nb090AlphaDummy431 A), (nb090AlphaDummy433 h)), ((nb090AlphaDummy461 A),
        (nb090AlphaDummy462 h)), ((nb090AlphaDummy435 A), (nb090AlphaDummy436 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A),
        (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy439 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy439 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy441 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy446
        A) ≠ (nb090AlphaDummy457 A) from (by
          unfold
            nb090AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0458
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy458 h) from (by
          unfold
            nb090AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0459
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠
        (nb090AlphaDummy455 A) from (by
          unfold
            nb090AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0456
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy456 h) from (by
          unfold
            nb090AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0457
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy439
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠ (nb090AlphaDummy457 A) from (by
          unfold
            nb090AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0458
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy458 h) from (by
          unfold
            nb090AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0459
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠
        (nb090AlphaDummy455 A) from (by
          unfold
            nb090AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0456
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy456 h) from (by
          unfold
            nb090AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0457
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy439
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy447
        A) ≠ (nb090AlphaDummy459 A) from (by
          unfold
            nb090AlphaDummy459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0462
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy460 h) from (by
          unfold
            nb090AlphaDummy460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0463
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠
        (nb090AlphaDummy455 A) from (by
          unfold
            nb090AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0460
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy456 h) from (by
          unfold
            nb090AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0461
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy447
        A) ≠ (nb090AlphaDummy459 A) from (by
          unfold
            nb090AlphaDummy459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0462
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy460 h) from (by
          unfold
            nb090AlphaDummy460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0463
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠
        (nb090AlphaDummy455 A) from (by
          unfold
            nb090AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0460
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy456 h) from (by
          unfold
            nb090AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0461
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy443 A) from
                                    (by
                                      unfold nb090AlphaDummy443;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0444 A)
                                              0)))) (show
                                    (nb090AlphaDummy441 h) ≠ (nb090AlphaDummy444 h) from
                                    (by
                                      unfold nb090AlphaDummy444;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0445 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb090AlphaDummy443 A), (nb090AlphaDummy444 h)),
                                  ((nb090AlphaDummy439 A), (nb090AlphaDummy441 h)),
                                  ((nb090AlphaDummy440 A), (nb090AlphaDummy442 h)),
                                  ((nb090AlphaDummy465 A), (nb090AlphaDummy466 h)),
                                  ((nb090AlphaDummy463 A), (nb090AlphaDummy464 h)),
                                  ((nb090AlphaDummy432 A), (nb090AlphaDummy434 h)),
                                  ((nb090AlphaDummy431 A), (nb090AlphaDummy433 h)),
                                  ((nb090AlphaDummy461 A), (nb090AlphaDummy462 h)),
                                  ((nb090AlphaDummy435 A), (nb090AlphaDummy436 h)),
                                  ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                  ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                  ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                  ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                  ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                  ((nb090AlphaDummy000 A), h),
                                  ((nb090AlphaDummy002 A), v),
                                  ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                    (nb090AlphaDummy004 v u A h))]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy443 A) from (by
                                    unfold nb090AlphaDummy443;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0444 A)
                                            0)))) (show
                                  (nb090AlphaDummy441 h) ≠ (nb090AlphaDummy444 h) from (by
                                    unfold nb090AlphaDummy444;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0445 h)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy443 A) from
                                    (by
                                      unfold nb090AlphaDummy443;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0444 A)
                                              0)))) (show
                                    (nb090AlphaDummy441 h) ≠ (nb090AlphaDummy444 h) from
                                    (by
                                      unfold nb090AlphaDummy444;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0445 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb090AlphaDummy443 A), (nb090AlphaDummy444 h)),
                                  ((nb090AlphaDummy439 A), (nb090AlphaDummy441 h)),
                                  ((nb090AlphaDummy440 A), (nb090AlphaDummy442 h)),
                                  ((nb090AlphaDummy465 A), (nb090AlphaDummy466 h)),
                                  ((nb090AlphaDummy463 A), (nb090AlphaDummy464 h)),
                                  ((nb090AlphaDummy432 A), (nb090AlphaDummy434 h)),
                                  ((nb090AlphaDummy431 A), (nb090AlphaDummy433 h)),
                                  ((nb090AlphaDummy461 A), (nb090AlphaDummy462 h)),
                                  ((nb090AlphaDummy435 A), (nb090AlphaDummy436 h)),
                                  ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                  ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                  ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                  ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                  ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                  ((nb090AlphaDummy000 A), h),
                                  ((nb090AlphaDummy002 A), v),
                                  ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                    (nb090AlphaDummy004 v u A h))]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb090AlphaDummy432 A) ≠ (nb090AlphaDummy439 A) from (by
                            unfold nb090AlphaDummy439;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0442 A) 0))))
                        (show (nb090AlphaDummy434 h) ≠ (nb090AlphaDummy441 h) from (by
                            unfold nb090AlphaDummy441;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0443 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy432 A) ≠ (nb090AlphaDummy440 A) from (by
                              unfold nb090AlphaDummy440;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0442 A) 1))))
                          (show (nb090AlphaDummy434 h) ≠ (nb090AlphaDummy442 h) from (by
                              unfold nb090AlphaDummy442;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0443 h) 1))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy432 A) ≠ (nb090AlphaDummy465 A) from (by
                                unfold nb090AlphaDummy465;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0472 A) 0))))
                            (show (nb090AlphaDummy434 h) ≠ (nb090AlphaDummy466 h) from (by
                                unfold nb090AlphaDummy466;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0473 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy432 A) ≠ (nb090AlphaDummy463 A) from
                                (by
                                  unfold nb090AlphaDummy463;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0470 A) 0))))
                              (show (nb090AlphaDummy434 h) ≠ (nb090AlphaDummy464 h) from
                                (by
                                  unfold nb090AlphaDummy464;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0471 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb090AlphaDummy432 A))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb090AlphaDummy434 h))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090AlphaDummy439 A) ≠
        (nb090AlphaDummy446 A) from (by
          unfold nb090AlphaDummy446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0446 A) 1)))) (show (nb090AlphaDummy441 h) ≠
        (nb090AlphaDummy449 h) from (by
          unfold nb090AlphaDummy449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0447 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy445 A) from (by
          unfold nb090AlphaDummy445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0446 A) 0)))) (show (nb090AlphaDummy441 h) ≠
        (nb090AlphaDummy448 h) from (by
          unfold nb090AlphaDummy448;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0447 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy443 A) from (by
          unfold nb090AlphaDummy443;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0444 A) 0)))) (show (nb090AlphaDummy441 h) ≠
        (nb090AlphaDummy444 h) from (by
          unfold nb090AlphaDummy444;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0445 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy447 A), (nb090AlphaDummy450 h)), ((nb090AlphaDummy446 A),
        (nb090AlphaDummy449 h)), ((nb090AlphaDummy445 A), (nb090AlphaDummy448 h)),
        ((nb090AlphaDummy443 A), (nb090AlphaDummy444 h)), ((nb090AlphaDummy439 A),
        (nb090AlphaDummy441 h)), ((nb090AlphaDummy440 A), (nb090AlphaDummy442 h)),
        ((nb090AlphaDummy465 A), (nb090AlphaDummy466 h)), ((nb090AlphaDummy463 A),
        (nb090AlphaDummy464 h)), ((nb090AlphaDummy432 A), (nb090AlphaDummy434 h)),
        ((nb090AlphaDummy431 A), (nb090AlphaDummy433 h)), ((nb090AlphaDummy461 A),
        (nb090AlphaDummy462 h)), ((nb090AlphaDummy435 A), (nb090AlphaDummy436 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A),
        (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠ (nb090AlphaDummy453 A) from (by
          unfold
            nb090AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0450
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy454 h) from (by
          unfold
            nb090AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0451
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠
        (nb090AlphaDummy451 A) from (by
          unfold
            nb090AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0448
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy452 h) from (by
          unfold
            nb090AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0449
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy439
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠ (nb090AlphaDummy453 A) from (by
          unfold
            nb090AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0454
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy454 h) from (by
          unfold
            nb090AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0455
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠
        (nb090AlphaDummy451 A) from (by
          unfold
            nb090AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0452
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy452 h) from (by
          unfold
            nb090AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0453
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠ (nb090AlphaDummy453 A) from (by
          unfold
            nb090AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0450
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy454 h) from (by
          unfold
            nb090AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0451
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠
        (nb090AlphaDummy451 A) from (by
          unfold
            nb090AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0448
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy452 h) from (by
          unfold
            nb090AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0449
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy439
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠ (nb090AlphaDummy453 A) from (by
          unfold
            nb090AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0454
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy454 h) from (by
          unfold
            nb090AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0455
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠
        (nb090AlphaDummy451 A) from (by
          unfold
            nb090AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0452
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy452 h) from (by
          unfold
            nb090AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0453
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy447 A), (nb090AlphaDummy450 h)), ((nb090AlphaDummy446 A),
        (nb090AlphaDummy449 h)), ((nb090AlphaDummy445 A), (nb090AlphaDummy448 h)),
        ((nb090AlphaDummy443 A), (nb090AlphaDummy444 h)), ((nb090AlphaDummy439 A),
        (nb090AlphaDummy441 h)), ((nb090AlphaDummy440 A), (nb090AlphaDummy442 h)),
        ((nb090AlphaDummy465 A), (nb090AlphaDummy466 h)), ((nb090AlphaDummy463 A),
        (nb090AlphaDummy464 h)), ((nb090AlphaDummy432 A), (nb090AlphaDummy434 h)),
        ((nb090AlphaDummy431 A), (nb090AlphaDummy433 h)), ((nb090AlphaDummy461 A),
        (nb090AlphaDummy462 h)), ((nb090AlphaDummy435 A), (nb090AlphaDummy436 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A),
        (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy439 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy439 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy441 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy446
        A) ≠ (nb090AlphaDummy457 A) from (by
          unfold
            nb090AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0458
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy458 h) from (by
          unfold
            nb090AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0459
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠
        (nb090AlphaDummy455 A) from (by
          unfold
            nb090AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0456
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy456 h) from (by
          unfold
            nb090AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0457
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy439
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠ (nb090AlphaDummy457 A) from (by
          unfold
            nb090AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0458
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy458 h) from (by
          unfold
            nb090AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0459
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy446 A) ≠
        (nb090AlphaDummy455 A) from (by
          unfold
            nb090AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0456
                    A)
                  0)))) (show (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy456 h) from (by
          unfold
            nb090AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0457
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy439
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy447
        A) ≠ (nb090AlphaDummy459 A) from (by
          unfold
            nb090AlphaDummy459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0462
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy460 h) from (by
          unfold
            nb090AlphaDummy460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0463
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠
        (nb090AlphaDummy455 A) from (by
          unfold
            nb090AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0460
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy456 h) from (by
          unfold
            nb090AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0461
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy447
        A) ≠ (nb090AlphaDummy459 A) from (by
          unfold
            nb090AlphaDummy459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0462
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy460 h) from (by
          unfold
            nb090AlphaDummy460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0463
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy447 A) ≠
        (nb090AlphaDummy455 A) from (by
          unfold
            nb090AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0460
                    A)
                  0)))) (show (nb090AlphaDummy450 h) ≠ (nb090AlphaDummy456 h) from (by
          unfold
            nb090AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0461
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy443 A) from
                                    (by
                                      unfold nb090AlphaDummy443;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0444 A)
                                              0)))) (show
                                    (nb090AlphaDummy441 h) ≠ (nb090AlphaDummy444 h) from
                                    (by
                                      unfold nb090AlphaDummy444;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0445 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb090AlphaDummy443 A), (nb090AlphaDummy444 h)),
                                  ((nb090AlphaDummy439 A), (nb090AlphaDummy441 h)),
                                  ((nb090AlphaDummy440 A), (nb090AlphaDummy442 h)),
                                  ((nb090AlphaDummy465 A), (nb090AlphaDummy466 h)),
                                  ((nb090AlphaDummy463 A), (nb090AlphaDummy464 h)),
                                  ((nb090AlphaDummy432 A), (nb090AlphaDummy434 h)),
                                  ((nb090AlphaDummy431 A), (nb090AlphaDummy433 h)),
                                  ((nb090AlphaDummy461 A), (nb090AlphaDummy462 h)),
                                  ((nb090AlphaDummy435 A), (nb090AlphaDummy436 h)),
                                  ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                  ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                  ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                  ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                  ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                  ((nb090AlphaDummy000 A), h),
                                  ((nb090AlphaDummy002 A), v),
                                  ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                    (nb090AlphaDummy004 v u A h))]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy443 A) from (by
                                    unfold nb090AlphaDummy443;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0444 A)
                                            0)))) (show
                                  (nb090AlphaDummy441 h) ≠ (nb090AlphaDummy444 h) from (by
                                    unfold nb090AlphaDummy444;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0445 h)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy443 A) from
                                    (by
                                      unfold nb090AlphaDummy443;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0444 A)
                                              0)))) (show
                                    (nb090AlphaDummy441 h) ≠ (nb090AlphaDummy444 h) from
                                    (by
                                      unfold nb090AlphaDummy444;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0445 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb090AlphaDummy443 A), (nb090AlphaDummy444 h)),
                                  ((nb090AlphaDummy439 A), (nb090AlphaDummy441 h)),
                                  ((nb090AlphaDummy440 A), (nb090AlphaDummy442 h)),
                                  ((nb090AlphaDummy465 A), (nb090AlphaDummy466 h)),
                                  ((nb090AlphaDummy463 A), (nb090AlphaDummy464 h)),
                                  ((nb090AlphaDummy432 A), (nb090AlphaDummy434 h)),
                                  ((nb090AlphaDummy431 A), (nb090AlphaDummy433 h)),
                                  ((nb090AlphaDummy461 A), (nb090AlphaDummy462 h)),
                                  ((nb090AlphaDummy435 A), (nb090AlphaDummy436 h)),
                                  ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                  ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                  ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                  ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                  ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                  ((nb090AlphaDummy000 A), h),
                                  ((nb090AlphaDummy002 A), v),
                                  ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                    (nb090AlphaDummy004 v u A h))]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part062`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0040`. -/
@[expose]
noncomputable def nb090SplitAlpha0040 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy473 A), (nb090AlphaDummy474 h)),
        ((nb090AlphaDummy471 A), (nb090AlphaDummy472 h)),
        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy473 A))
          (Class.cab (nb090AlphaDummy467 A)
            (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy423 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                (synCphi (Class.cv (nb090AlphaDummy468 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy473 A))
            (Class.cab (nb090AlphaDummy467 A)
              (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy423 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                  (synCphi (Class.cv (nb090AlphaDummy468 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy474 h))
          (Class.cab (nb090AlphaDummy469 h)
            (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy426 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                (synCphi (Class.cv (nb090AlphaDummy470 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy474 h))
            (Class.cab (nb090AlphaDummy469 h)
              (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy426 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                  (synCphi (Class.cv (nb090AlphaDummy470 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy468 A) from (by
                      unfold nb090AlphaDummy468;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0474 A) 1))))
                  (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy470 h) from (by
                      unfold nb090AlphaDummy470;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0476 h) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy467 A) from (by
                        unfold nb090AlphaDummy467;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0474 A) 0))))
                    (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy469 h) from (by
                        unfold nb090AlphaDummy469;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0476 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy473 A) from (by
                          unfold nb090AlphaDummy473;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0478 A) 0))))
                      (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy474 h) from (by
                          unfold nb090AlphaDummy474;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0479 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy471 A) from (by
                            unfold nb090AlphaDummy471;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0475 A) 0))))
                        (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy472 h) from (by
                            unfold nb090AlphaDummy472;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0477 h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪ ((synCcnv
                                  (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv)
                            (by decide)) (freshVar_injective (((synCcnv (Class.cv h))).fv ∪
                              ((synCcnv (synCcnv (Class.cv h)))).fv) (by decide))
                          (TAlphaVar.there (freshVar_injective
                              (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪ ((synCcnv
                                    (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv)
                              (by decide)) (freshVar_injective (((synCcnv (Class.cv h))).fv ∪
                                ((synCcnv (synCcnv (Class.cv h)))).fv) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy423 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy425 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090AlphaDummy426 h))).fv ∪
                      ((Class.cv (nb090AlphaDummy428 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy468 A) ≠ (nb090AlphaDummy475 A) from (by
                              unfold nb090AlphaDummy475;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0480 A) 0))))
                          (show (nb090AlphaDummy470 h) ≠ (nb090AlphaDummy477 h) from (by
                              unfold nb090AlphaDummy477;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0481 h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy468 A) ≠ (nb090AlphaDummy476 A) from (by
                                unfold nb090AlphaDummy476;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0480 A) 1))))
                            (show (nb090AlphaDummy470 h) ≠ (nb090AlphaDummy478 h) from (by
                                unfold nb090AlphaDummy478;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0481 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy468 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy470 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy482 A) from (by
          unfold nb090AlphaDummy482;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0484 A) 1)))) (show (nb090AlphaDummy477 h) ≠
        (nb090AlphaDummy485 h) from (by
          unfold nb090AlphaDummy485;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0485 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy481 A) from (by
          unfold nb090AlphaDummy481;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0484 A) 0)))) (show (nb090AlphaDummy477 h) ≠
        (nb090AlphaDummy484 h) from (by
          unfold nb090AlphaDummy484;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0485 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy479 A) from (by
          unfold nb090AlphaDummy479;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0482 A)
                  0)))) (show (nb090AlphaDummy477 h) ≠ (nb090AlphaDummy480 h) from (by
          unfold nb090AlphaDummy480;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0483 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy483 A), (nb090AlphaDummy486 h)), ((nb090AlphaDummy482 A),
        (nb090AlphaDummy485 h)), ((nb090AlphaDummy481 A), (nb090AlphaDummy484 h)),
        ((nb090AlphaDummy479 A), (nb090AlphaDummy480 h)), ((nb090AlphaDummy475 A),
        (nb090AlphaDummy477 h)), ((nb090AlphaDummy476 A), (nb090AlphaDummy478 h)),
        ((nb090AlphaDummy468 A), (nb090AlphaDummy470 h)), ((nb090AlphaDummy467 A),
        (nb090AlphaDummy469 h)), ((nb090AlphaDummy473 A), (nb090AlphaDummy474 h)),
        ((nb090AlphaDummy471 A), (nb090AlphaDummy472 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠ (nb090AlphaDummy489 A) from (by
          unfold
            nb090AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0488
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy490 h) from (by
          unfold
            nb090AlphaDummy490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0489
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠
        (nb090AlphaDummy487 A) from (by
          unfold
            nb090AlphaDummy487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0486
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy488 h) from (by
          unfold
            nb090AlphaDummy488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0487
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy475
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠ (nb090AlphaDummy489 A) from (by
          unfold
            nb090AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0492
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy490 h) from (by
          unfold
            nb090AlphaDummy490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0493
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠
        (nb090AlphaDummy487 A) from (by
          unfold
            nb090AlphaDummy487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0490
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy488 h) from (by
          unfold
            nb090AlphaDummy488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0491
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠ (nb090AlphaDummy489 A) from (by
          unfold
            nb090AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0488
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy490 h) from (by
          unfold
            nb090AlphaDummy490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0489
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠
        (nb090AlphaDummy487 A) from (by
          unfold
            nb090AlphaDummy487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0486
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy488 h) from (by
          unfold
            nb090AlphaDummy488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0487
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy475
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠ (nb090AlphaDummy489 A) from (by
          unfold
            nb090AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0492
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy490 h) from (by
          unfold
            nb090AlphaDummy490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0493
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠
        (nb090AlphaDummy487 A) from (by
          unfold
            nb090AlphaDummy487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0490
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy488 h) from (by
          unfold
            nb090AlphaDummy488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0491
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy483 A), (nb090AlphaDummy486 h)), ((nb090AlphaDummy482 A),
        (nb090AlphaDummy485 h)), ((nb090AlphaDummy481 A), (nb090AlphaDummy484 h)),
        ((nb090AlphaDummy479 A), (nb090AlphaDummy480 h)), ((nb090AlphaDummy475 A),
        (nb090AlphaDummy477 h)), ((nb090AlphaDummy476 A), (nb090AlphaDummy478 h)),
        ((nb090AlphaDummy468 A), (nb090AlphaDummy470 h)), ((nb090AlphaDummy467 A),
        (nb090AlphaDummy469 h)), ((nb090AlphaDummy473 A), (nb090AlphaDummy474 h)),
        ((nb090AlphaDummy471 A), (nb090AlphaDummy472 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy475 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy475 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy477 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy482
        A) ≠ (nb090AlphaDummy493 A) from (by
          unfold
            nb090AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0496
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy494 h) from (by
          unfold
            nb090AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0497
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠
        (nb090AlphaDummy491 A) from (by
          unfold
            nb090AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0494
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy492 h) from (by
          unfold
            nb090AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0495
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy475
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠ (nb090AlphaDummy493 A) from (by
          unfold
            nb090AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0496
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy494 h) from (by
          unfold
            nb090AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0497
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠
        (nb090AlphaDummy491 A) from (by
          unfold
            nb090AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0494
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy492 h) from (by
          unfold
            nb090AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0495
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy475
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy483
        A) ≠ (nb090AlphaDummy495 A) from (by
          unfold
            nb090AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0500
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy496 h) from (by
          unfold
            nb090AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0501
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠
        (nb090AlphaDummy491 A) from (by
          unfold
            nb090AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0498
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy492 h) from (by
          unfold
            nb090AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0499
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy483
        A) ≠ (nb090AlphaDummy495 A) from (by
          unfold
            nb090AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0500
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy496 h) from (by
          unfold
            nb090AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0501
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠
        (nb090AlphaDummy491 A) from (by
          unfold
            nb090AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0498
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy492 h) from (by
          unfold
            nb090AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0499
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy479 A) from
                                      (by
                                        unfold nb090AlphaDummy479;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0482 A)
                                                0)))) (show (nb090AlphaDummy477 h) ≠
                                        (nb090AlphaDummy480 h) from (by
                                        unfold nb090AlphaDummy480;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0483 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy479 A), (nb090AlphaDummy480 h)),
                                    ((nb090AlphaDummy475 A), (nb090AlphaDummy477 h)),
                                    ((nb090AlphaDummy476 A), (nb090AlphaDummy478 h)),
                                    ((nb090AlphaDummy468 A), (nb090AlphaDummy470 h)),
                                    ((nb090AlphaDummy467 A), (nb090AlphaDummy469 h)),
                                    ((nb090AlphaDummy473 A), (nb090AlphaDummy474 h)),
                                    ((nb090AlphaDummy471 A), (nb090AlphaDummy472 h)),
                                    ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                    ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                    ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                    ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                    ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                    ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy479 A) from
                                    (by
                                      unfold nb090AlphaDummy479;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0482 A)
                                              0)))) (show
                                    (nb090AlphaDummy477 h) ≠ (nb090AlphaDummy480 h) from
                                    (by
                                      unfold nb090AlphaDummy480;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0483 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy479 A) from
                                      (by
                                        unfold nb090AlphaDummy479;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0482 A)
                                                0)))) (show (nb090AlphaDummy477 h) ≠
                                        (nb090AlphaDummy480 h) from (by
                                        unfold nb090AlphaDummy480;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0483 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy479 A), (nb090AlphaDummy480 h)),
                                    ((nb090AlphaDummy475 A), (nb090AlphaDummy477 h)),
                                    ((nb090AlphaDummy476 A), (nb090AlphaDummy478 h)),
                                    ((nb090AlphaDummy468 A), (nb090AlphaDummy470 h)),
                                    ((nb090AlphaDummy467 A), (nb090AlphaDummy469 h)),
                                    ((nb090AlphaDummy473 A), (nb090AlphaDummy474 h)),
                                    ((nb090AlphaDummy471 A), (nb090AlphaDummy472 h)),
                                    ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                    ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                    ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                    ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                    ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                    ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy468 A) from (by
                        unfold nb090AlphaDummy468;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0474 A) 1))))
                    (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy470 h) from (by
                        unfold nb090AlphaDummy470;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0476 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy467 A) from (by
                          unfold nb090AlphaDummy467;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0474 A) 0))))
                      (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy469 h) from (by
                          unfold nb090AlphaDummy469;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0476 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy473 A) from (by
                            unfold nb090AlphaDummy473;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0478 A) 0))))
                        (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy474 h) from (by
                            unfold nb090AlphaDummy474;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0479 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy471 A) from (by
                              unfold nb090AlphaDummy471;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0475 A) 0))))
                          (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy472 h) from (by
                              unfold nb090AlphaDummy472;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0477 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪ ((synCcnv
                                    (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv)
                              (by decide)) (freshVar_injective (((synCcnv (Class.cv h))).fv ∪
                                ((synCcnv (synCcnv (Class.cv h)))).fv) (by decide))
                            (TAlphaVar.there (freshVar_injective
                                (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪
                                  ((synCcnv (synCcnv
                                        (Class.cv (nb090AlphaDummy000 A))))).fv) (by decide))
                              (freshVar_injective (((synCcnv (Class.cv h))).fv ∪
                                  ((synCcnv (synCcnv (Class.cv h)))).fv) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy423 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy425 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy426 h))).fv ∪
                        ((Class.cv (nb090AlphaDummy428 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy468 A) ≠ (nb090AlphaDummy475 A) from (by
                                unfold nb090AlphaDummy475;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0480 A) 0))))
                            (show (nb090AlphaDummy470 h) ≠ (nb090AlphaDummy477 h) from (by
                                unfold nb090AlphaDummy477;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0481 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy468 A) ≠ (nb090AlphaDummy476 A) from
                                (by
                                  unfold nb090AlphaDummy476;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0480 A) 1))))
                              (show (nb090AlphaDummy470 h) ≠ (nb090AlphaDummy478 h) from
                                (by
                                  unfold nb090AlphaDummy478;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0481 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy468 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy470 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy482 A) from (by
          unfold nb090AlphaDummy482;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0484 A) 1)))) (show (nb090AlphaDummy477 h) ≠
        (nb090AlphaDummy485 h) from (by
          unfold nb090AlphaDummy485;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0485 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy481 A) from (by
          unfold nb090AlphaDummy481;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0484 A)
                  0)))) (show (nb090AlphaDummy477 h) ≠ (nb090AlphaDummy484 h) from (by
          unfold nb090AlphaDummy484;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0485 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy475 A) ≠
        (nb090AlphaDummy479 A) from (by
          unfold nb090AlphaDummy479;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0482 A)
                  0)))) (show (nb090AlphaDummy477 h) ≠ (nb090AlphaDummy480 h) from (by
          unfold nb090AlphaDummy480;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0483 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy483 A), (nb090AlphaDummy486 h)), ((nb090AlphaDummy482 A),
        (nb090AlphaDummy485 h)), ((nb090AlphaDummy481 A), (nb090AlphaDummy484 h)),
        ((nb090AlphaDummy479 A), (nb090AlphaDummy480 h)), ((nb090AlphaDummy475 A),
        (nb090AlphaDummy477 h)), ((nb090AlphaDummy476 A), (nb090AlphaDummy478 h)),
        ((nb090AlphaDummy468 A), (nb090AlphaDummy470 h)), ((nb090AlphaDummy467 A),
        (nb090AlphaDummy469 h)), ((nb090AlphaDummy473 A), (nb090AlphaDummy474 h)),
        ((nb090AlphaDummy471 A), (nb090AlphaDummy472 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠ (nb090AlphaDummy489 A) from (by
          unfold
            nb090AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0488
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy490 h) from (by
          unfold
            nb090AlphaDummy490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0489
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠
        (nb090AlphaDummy487 A) from (by
          unfold
            nb090AlphaDummy487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0486
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy488 h) from (by
          unfold
            nb090AlphaDummy488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0487
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy475
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠ (nb090AlphaDummy489 A) from (by
          unfold
            nb090AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0492
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy490 h) from (by
          unfold
            nb090AlphaDummy490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0493
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠
        (nb090AlphaDummy487 A) from (by
          unfold
            nb090AlphaDummy487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0490
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy488 h) from (by
          unfold
            nb090AlphaDummy488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0491
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠ (nb090AlphaDummy489 A) from (by
          unfold
            nb090AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0488
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy490 h) from (by
          unfold
            nb090AlphaDummy490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0489
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠
        (nb090AlphaDummy487 A) from (by
          unfold
            nb090AlphaDummy487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0486
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy488 h) from (by
          unfold
            nb090AlphaDummy488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0487
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy475
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠ (nb090AlphaDummy489 A) from (by
          unfold
            nb090AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0492
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy490 h) from (by
          unfold
            nb090AlphaDummy490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0493
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠
        (nb090AlphaDummy487 A) from (by
          unfold
            nb090AlphaDummy487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0490
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy488 h) from (by
          unfold
            nb090AlphaDummy488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0491
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy483 A), (nb090AlphaDummy486 h)), ((nb090AlphaDummy482 A),
        (nb090AlphaDummy485 h)), ((nb090AlphaDummy481 A), (nb090AlphaDummy484 h)),
        ((nb090AlphaDummy479 A), (nb090AlphaDummy480 h)), ((nb090AlphaDummy475 A),
        (nb090AlphaDummy477 h)), ((nb090AlphaDummy476 A), (nb090AlphaDummy478 h)),
        ((nb090AlphaDummy468 A), (nb090AlphaDummy470 h)), ((nb090AlphaDummy467 A),
        (nb090AlphaDummy469 h)), ((nb090AlphaDummy473 A), (nb090AlphaDummy474 h)),
        ((nb090AlphaDummy471 A), (nb090AlphaDummy472 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy475 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy477
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy475 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy482
        A) ≠ (nb090AlphaDummy493 A) from (by
          unfold
            nb090AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0496
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy494 h) from (by
          unfold
            nb090AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0497
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠
        (nb090AlphaDummy491 A) from (by
          unfold
            nb090AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0494
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy492 h) from (by
          unfold
            nb090AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0495
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy475
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠ (nb090AlphaDummy493 A) from (by
          unfold
            nb090AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0496
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy494 h) from (by
          unfold
            nb090AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0497
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠
        (nb090AlphaDummy491 A) from (by
          unfold
            nb090AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0494
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy492 h) from (by
          unfold
            nb090AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0495
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy475
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy483
        A) ≠ (nb090AlphaDummy495 A) from (by
          unfold
            nb090AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0500
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy496 h) from (by
          unfold
            nb090AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0501
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠
        (nb090AlphaDummy491 A) from (by
          unfold
            nb090AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0498
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy492 h) from (by
          unfold
            nb090AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0499
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy483
        A) ≠ (nb090AlphaDummy495 A) from (by
          unfold
            nb090AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0500
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy496 h) from (by
          unfold
            nb090AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0501
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠
        (nb090AlphaDummy491 A) from (by
          unfold
            nb090AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0498
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy492 h) from (by
          unfold
            nb090AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0499
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy479 A)
                                        from (by
                                          unfold nb090AlphaDummy479;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0482 A) 0)))) (show
                                        (nb090AlphaDummy477 h) ≠ (nb090AlphaDummy480 h)
                                        from (by
                                          unfold nb090AlphaDummy480;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0483 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy479 A), (nb090AlphaDummy480 h)),
                                      ((nb090AlphaDummy475 A), (nb090AlphaDummy477 h)),
                                      ((nb090AlphaDummy476 A), (nb090AlphaDummy478 h)),
                                      ((nb090AlphaDummy468 A), (nb090AlphaDummy470 h)),
                                      ((nb090AlphaDummy467 A), (nb090AlphaDummy469 h)),
                                      ((nb090AlphaDummy473 A), (nb090AlphaDummy474 h)),
                                      ((nb090AlphaDummy471 A), (nb090AlphaDummy472 h)),
                                      ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                      ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                      ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                      ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                      ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                      ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy479 A) from
                                      (by
                                        unfold nb090AlphaDummy479;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0482 A)
                                                0)))) (show (nb090AlphaDummy477 h) ≠
                                        (nb090AlphaDummy480 h) from (by
                                        unfold nb090AlphaDummy480;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0483 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy479 A)
                                        from (by
                                          unfold nb090AlphaDummy479;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0482 A) 0)))) (show
                                        (nb090AlphaDummy477 h) ≠ (nb090AlphaDummy480 h)
                                        from (by
                                          unfold nb090AlphaDummy480;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0483 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy479 A), (nb090AlphaDummy480 h)),
                                      ((nb090AlphaDummy475 A), (nb090AlphaDummy477 h)),
                                      ((nb090AlphaDummy476 A), (nb090AlphaDummy478 h)),
                                      ((nb090AlphaDummy468 A), (nb090AlphaDummy470 h)),
                                      ((nb090AlphaDummy467 A), (nb090AlphaDummy469 h)),
                                      ((nb090AlphaDummy473 A), (nb090AlphaDummy474 h)),
                                      ((nb090AlphaDummy471 A), (nb090AlphaDummy472 h)),
                                      ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                      ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                      ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                      ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                      ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                      ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
