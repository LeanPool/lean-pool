/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block031

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part092`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0070`. -/
@[expose]
noncomputable def nb090SplitAlpha0070 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.classMem (synCop (Class.cv (nb090AlphaDummy423 A))
          (Class.cv (nb090AlphaDummy425 A)))
        (synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A)))))
      (Wff.classMem (synCop (Class.cv (nb090AlphaDummy426 h))
          (Class.cv (nb090AlphaDummy428 h))) (synCcnv (synCcnv (Class.cv h)))) :=
  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0060 v u A h)))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy468 A) from (by
                                    unfold nb090AlphaDummy468;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0502 A)
                                            1)))) (show
                                  (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy470 h) from (by
                                    unfold nb090AlphaDummy470;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0504 h)
                                            1)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy467 A) from
                                    (by
                                      unfold nb090AlphaDummy467;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0502 A)
                                              0)))) (show
                                    (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy469 h) from
                                    (by
                                      unfold nb090AlphaDummy469;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0504 h)
                                              0)))) (TAlphaVar.there (show
                                      (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy497 A) from
                                      (by
                                        unfold nb090AlphaDummy497;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0506 A)
                                                0)))) (show (nb090AlphaDummy428 h) ≠
                                        (nb090AlphaDummy498 h) from (by
                                        unfold nb090AlphaDummy498;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0507 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy471 A)
                                        from (by
                                          unfold nb090AlphaDummy471;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0503 A) 0)))) (show
                                        (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy472 h)
                                        from (by
                                          unfold nb090AlphaDummy472;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0505 h) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb090AlphaDummy423 A))).fv ∪
                                    ((Class.cv (nb090AlphaDummy425 A))).fv) (by decide))
                                (freshVar_injective (((Class.cv (nb090AlphaDummy426 h))).fv ∪
                                    ((Class.cv (nb090AlphaDummy428 h))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb090SplitAlpha0061 v u A h)))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy468 A) from (by
                                    unfold nb090AlphaDummy468;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0502 A)
                                            1)))) (show
                                  (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy470 h) from (by
                                    unfold nb090AlphaDummy470;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0504 h)
                                            1)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy467 A) from
                                    (by
                                      unfold nb090AlphaDummy467;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0502 A)
                                              0)))) (show
                                    (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy469 h) from
                                    (by
                                      unfold nb090AlphaDummy469;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0504 h)
                                              0)))) (TAlphaVar.there (show
                                      (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy497 A) from
                                      (by
                                        unfold nb090AlphaDummy497;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0506 A)
                                                0)))) (show (nb090AlphaDummy428 h) ≠
                                        (nb090AlphaDummy498 h) from (by
                                        unfold nb090AlphaDummy498;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0507 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy471 A)
                                        from (by
                                          unfold nb090AlphaDummy471;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0503 A) 0)))) (show
                                        (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy472 h)
                                        from (by
                                          unfold nb090AlphaDummy472;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0505 h) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb090AlphaDummy423 A))).fv ∪
                                    ((Class.cv (nb090AlphaDummy425 A))).fv) (by decide))
                                (freshVar_injective (((Class.cv (nb090AlphaDummy426 h))).fv ∪
                                    ((Class.cv (nb090AlphaDummy428 h))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb090SplitAlpha0061 v u A h))))))))))))))))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                    (show (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy507 A) from (by
                        unfold nb090AlphaDummy507;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0514 A) 0))))) (Ne.symm
                    (show (nb090AlphaDummy506 h) ≠ (nb090AlphaDummy508 h) from (by
                        unfold nb090AlphaDummy508;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0515 h) 0)))))
                  (TAlphaVar.there (Ne.symm
                      (show (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy507 A) from (by
                          unfold nb090AlphaDummy507;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0512 A) 0))))) (Ne.symm
                      (show (nb090AlphaDummy505 h) ≠ (nb090AlphaDummy508 h) from (by
                          unfold nb090AlphaDummy508;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0513 h) 0)))))
                    (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0062 v u A h)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090AlphaDummy504 A) ≠
        (nb090AlphaDummy510 A) from (by
          unfold nb090AlphaDummy510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0544 A) 1)))) (show (nb090AlphaDummy506 h) ≠
        (nb090AlphaDummy512 h) from (by
          unfold nb090AlphaDummy512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0546 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy509 A) from (by
          unfold nb090AlphaDummy509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0544 A) 0)))) (show (nb090AlphaDummy506 h) ≠
        (nb090AlphaDummy511 h) from (by
          unfold nb090AlphaDummy511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0546 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy539 A) from (by
          unfold nb090AlphaDummy539;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0548 A) 0)))) (show (nb090AlphaDummy506 h) ≠
        (nb090AlphaDummy540 h) from (by
          unfold nb090AlphaDummy540;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0549 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy513 A) from (by
          unfold nb090AlphaDummy513;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0545 A)
                  0)))) (show (nb090AlphaDummy506 h) ≠ (nb090AlphaDummy514 h) from (by
          unfold nb090AlphaDummy514;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0547 h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy503 A))).fv ∪ ((Class.cv (nb090AlphaDummy504 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy505 h))).fv ∪
        ((Class.cv (nb090AlphaDummy506 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0063 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy541 A), (nb090AlphaDummy542 h)), ((nb090AlphaDummy510 A),
        (nb090AlphaDummy512 h)), ((nb090AlphaDummy509 A), (nb090AlphaDummy511 h)),
        ((nb090AlphaDummy539 A), (nb090AlphaDummy540 h)), ((nb090AlphaDummy513 A),
        (nb090AlphaDummy514 h)), ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
        ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)), ((nb090AlphaDummy507 A),
        (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090AlphaDummy504 A) ≠
        (nb090AlphaDummy510 A) from (by
          unfold nb090AlphaDummy510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0544 A) 1)))) (show (nb090AlphaDummy506 h) ≠
        (nb090AlphaDummy512 h) from (by
          unfold nb090AlphaDummy512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0546 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy509 A) from (by
          unfold nb090AlphaDummy509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0544 A) 0)))) (show (nb090AlphaDummy506 h) ≠
        (nb090AlphaDummy511 h) from (by
          unfold nb090AlphaDummy511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0546 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy539 A) from (by
          unfold nb090AlphaDummy539;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0548 A) 0)))) (show (nb090AlphaDummy506 h) ≠
        (nb090AlphaDummy540 h) from (by
          unfold nb090AlphaDummy540;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0549 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy513 A) from (by
          unfold nb090AlphaDummy513;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0545 A)
                  0)))) (show (nb090AlphaDummy506 h) ≠ (nb090AlphaDummy514 h) from (by
          unfold nb090AlphaDummy514;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0547 h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy503 A))).fv ∪ ((Class.cv (nb090AlphaDummy504 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy505 h))).fv ∪
        ((Class.cv (nb090AlphaDummy506 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0063 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy541 A), (nb090AlphaDummy542 h)), ((nb090AlphaDummy510 A),
        (nb090AlphaDummy512 h)), ((nb090AlphaDummy509 A), (nb090AlphaDummy511 h)),
        ((nb090AlphaDummy539 A), (nb090AlphaDummy540 h)), ((nb090AlphaDummy513 A),
        (nb090AlphaDummy514 h)), ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
        ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)), ((nb090AlphaDummy507 A),
        (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0064 v u A h)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090AlphaDummy503 A) ≠
        (nb090AlphaDummy546 A) from (by
          unfold nb090AlphaDummy546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0582 A) 1)))) (show (nb090AlphaDummy505 h) ≠
        (nb090AlphaDummy548 h) from (by
          unfold nb090AlphaDummy548;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0584 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy545 A) from (by
          unfold nb090AlphaDummy545;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0582 A) 0)))) (show (nb090AlphaDummy505 h) ≠
        (nb090AlphaDummy547 h) from (by
          unfold nb090AlphaDummy547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0584 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy575 A) from (by
          unfold nb090AlphaDummy575;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0586 A) 0)))) (show (nb090AlphaDummy505 h) ≠
        (nb090AlphaDummy576 h) from (by
          unfold nb090AlphaDummy576;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0587 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy549 A) from (by
          unfold nb090AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0583 A)
                  0)))) (show (nb090AlphaDummy505 h) ≠ (nb090AlphaDummy550 h) from (by
          unfold nb090AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0585 h)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (Class.cv
        (nb090AlphaDummy000 A)))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv h))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy504 A))).fv ∪
        ((Class.cv (nb090AlphaDummy503 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy506 h))).fv ∪ ((Class.cv (nb090AlphaDummy505 h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0065 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy577 A), (nb090AlphaDummy578 h)), ((nb090AlphaDummy546 A),
        (nb090AlphaDummy548 h)), ((nb090AlphaDummy545 A), (nb090AlphaDummy547 h)),
        ((nb090AlphaDummy575 A), (nb090AlphaDummy576 h)), ((nb090AlphaDummy549 A),
        (nb090AlphaDummy550 h)), ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
        ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)), ((nb090AlphaDummy507 A),
        (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090AlphaDummy503 A) ≠
        (nb090AlphaDummy546 A) from (by
          unfold nb090AlphaDummy546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0582 A) 1)))) (show (nb090AlphaDummy505 h) ≠
        (nb090AlphaDummy548 h) from (by
          unfold nb090AlphaDummy548;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0584 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy545 A) from (by
          unfold nb090AlphaDummy545;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0582 A) 0)))) (show (nb090AlphaDummy505 h) ≠
        (nb090AlphaDummy547 h) from (by
          unfold nb090AlphaDummy547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0584 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy575 A) from (by
          unfold nb090AlphaDummy575;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0586 A) 0)))) (show (nb090AlphaDummy505 h) ≠
        (nb090AlphaDummy576 h) from (by
          unfold nb090AlphaDummy576;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0587 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy549 A) from (by
          unfold nb090AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0583 A)
                  0)))) (show (nb090AlphaDummy505 h) ≠ (nb090AlphaDummy550 h) from (by
          unfold nb090AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0585 h)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (Class.cv
        (nb090AlphaDummy000 A)))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv h))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy504 A))).fv ∪
        ((Class.cv (nb090AlphaDummy503 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy506 h))).fv ∪ ((Class.cv (nb090AlphaDummy505 h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0065 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy577 A), (nb090AlphaDummy578 h)), ((nb090AlphaDummy546 A),
        (nb090AlphaDummy548 h)), ((nb090AlphaDummy545 A), (nb090AlphaDummy547 h)),
        ((nb090AlphaDummy575 A), (nb090AlphaDummy576 h)), ((nb090AlphaDummy549 A),
        (nb090AlphaDummy550 h)), ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
        ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)), ((nb090AlphaDummy507 A),
        (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                              (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy133 A) from
                                (by
                                  unfold nb090AlphaDummy133;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0124 A) 0)))))
                            (Ne.symm (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy134 h)
                                from (by
                                  unfold nb090AlphaDummy134;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0125 h) 0)))))
                            (TAlphaVar.there (Ne.symm (show
                                  (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy133 A) from (by
                                    unfold nb090AlphaDummy133;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0122 A)
                                            0))))) (Ne.symm (show
                                  (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy134 h) from (by
                                    unfold nb090AlphaDummy134;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0123 h)
                                            0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb090SplitAlpha0066 v u A h)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy136 A) from (by
          unfold nb090AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154 A)
                  1)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy138 h) from (by
          unfold nb090AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156 h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy135 A) from (by
          unfold nb090AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy137 h) from (by
          unfold nb090AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy165 A) from (by
          unfold nb090AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0158
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy166 h) from (by
          unfold nb090AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0159
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy139 A) from (by
          unfold
            nb090AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0155
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy140 h) from (by
          unfold
            nb090AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0157
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy129 A))).fv ∪
        ((Class.cv (nb090AlphaDummy130 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy131 h))).fv ∪ ((Class.cv (nb090AlphaDummy132 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0067 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A),
        (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
        ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A),
        (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
        ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)), ((nb090AlphaDummy507 A),
        (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A
        h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy136 A) from (by
          unfold nb090AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154 A)
                  1)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy138 h) from (by
          unfold nb090AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156 h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy135 A) from (by
          unfold nb090AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy137 h) from (by
          unfold nb090AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy165 A) from (by
          unfold nb090AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0158
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy166 h) from (by
          unfold nb090AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0159
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy139 A) from (by
          unfold
            nb090AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0155
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy140 h) from (by
          unfold
            nb090AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0157
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy129 A))).fv ∪
        ((Class.cv (nb090AlphaDummy130 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy131 h))).fv ∪ ((Class.cv (nb090AlphaDummy132 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0067 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A),
        (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
        ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A),
        (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
        ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)), ((nb090AlphaDummy507 A),
        (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A
        h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb090SplitAlpha0068 v u A h)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy172 A) from (by
          unfold nb090AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192 A)
                  1)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy174 h) from (by
          unfold nb090AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194 h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy171 A) from (by
          unfold nb090AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy173 h) from (by
          unfold nb090AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy201 A) from (by
          unfold nb090AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0196
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy202 h) from (by
          unfold nb090AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0197
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy175 A) from (by
          unfold
            nb090AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0193
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy176 h) from (by
          unfold
            nb090AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0195
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy000
        A))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy130 A))).fv ∪ ((Class.cv
        (nb090AlphaDummy129 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy132 h))).fv ∪ ((Class.cv (nb090AlphaDummy131 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0069 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)), ((nb090AlphaDummy172 A),
        (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
        ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)), ((nb090AlphaDummy175 A),
        (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
        ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)), ((nb090AlphaDummy507 A),
        (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A
        h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy172 A) from (by
          unfold nb090AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192 A)
                  1)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy174 h) from (by
          unfold nb090AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194 h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy171 A) from (by
          unfold nb090AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy173 h) from (by
          unfold nb090AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy201 A) from (by
          unfold nb090AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0196
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy202 h) from (by
          unfold nb090AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0197
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy175 A) from (by
          unfold
            nb090AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0193
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy176 h) from (by
          unfold
            nb090AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0195
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy000
        A))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy130 A))).fv ∪ ((Class.cv
        (nb090AlphaDummy129 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy132 h))).fv ∪ ((Class.cv (nb090AlphaDummy131 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0069 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)), ((nb090AlphaDummy172 A),
        (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
        ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)), ((nb090AlphaDummy175 A),
        (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
        ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)), ((nb090AlphaDummy507 A),
        (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A
        h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy130 A) from (by
                                unfold nb090AlphaDummy130;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0212 A) 1))))
                            (show h ≠ (nb090AlphaDummy132 h) from (by
                                unfold nb090AlphaDummy132;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0213 h) 1))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy129 A) from
                                (by
                                  unfold nb090AlphaDummy129;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0212 A) 0))))
                              (show h ≠ (nb090AlphaDummy131 h) from (by
                                  unfold nb090AlphaDummy131;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0213 h) 0))))
                              (TAlphaVar.there (show
                                  (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy133 A) from (by
                                    unfold nb090AlphaDummy133;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0210 A)
                                            0)))) (show h ≠ (nb090AlphaDummy134 h) from (by
                                    unfold nb090AlphaDummy134;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0211 h)
                                            0)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy504 A) from
                                    (by
                                      unfold nb090AlphaDummy504;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0602 A)
                                              1)))) (show h ≠ (nb090AlphaDummy506 h) from (by
                                      unfold nb090AlphaDummy506;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0603 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy503 A) from
                                      (by
                                        unfold nb090AlphaDummy503;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0602 A)
                                                0)))) (show h ≠ (nb090AlphaDummy505 h) from
                                      (by
                                        unfold nb090AlphaDummy505;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0603 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy507 A)
                                        from (by
                                          unfold nb090AlphaDummy507;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0600 A) 0))))
                                      (show h ≠ (nb090AlphaDummy508 h) from (by
                                          unfold nb090AlphaDummy508;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0601 h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy425 A) from (by
          unfold nb090AlphaDummy425;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0596 A) 2)))) (show h ≠ (nb090AlphaDummy428 h) from (by
          unfold nb090AlphaDummy428;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0598 h) 2)))) (TAlphaVar.there (show
        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy424 A) from (by
          unfold nb090AlphaDummy424;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0596 A) 1)))) (show h ≠ (nb090AlphaDummy427 h) from (by
          unfold nb090AlphaDummy427;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0598 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy423 A) from (by
          unfold nb090AlphaDummy423;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0596 A) 0)))) (show h ≠ (nb090AlphaDummy426 h) from (by
          unfold nb090AlphaDummy426;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0598 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy429 A) from (by
          unfold nb090AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0597 A) 0)))) (show h ≠ (nb090AlphaDummy430 h) from (by
          unfold nb090AlphaDummy430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0599 h) 0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part093`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0071`. -/
@[expose]
noncomputable def nb090SplitAlpha0071 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy587 A), (nb090AlphaDummy588 h)),
        ((nb090AlphaDummy585 A), (nb090AlphaDummy586 h)),
        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy587 A))
          (Class.cab (nb090AlphaDummy581 A)
            (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy425 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                (synCphi (Class.cv (nb090AlphaDummy582 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy587 A))
            (Class.cab (nb090AlphaDummy581 A)
              (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy425 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                  (synCphi (Class.cv (nb090AlphaDummy582 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy588 h))
          (Class.cab (nb090AlphaDummy583 h)
            (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy428 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                (synCphi (Class.cv (nb090AlphaDummy584 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy588 h))
            (Class.cab (nb090AlphaDummy583 h)
              (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy428 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                  (synCphi (Class.cv (nb090AlphaDummy584 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy582 A) from (by
                      unfold nb090AlphaDummy582;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0604 A) 1))))
                  (show (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy584 h) from (by
                      unfold nb090AlphaDummy584;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0606 h) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy581 A) from (by
                        unfold nb090AlphaDummy581;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0604 A) 0))))
                    (show (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy583 h) from (by
                        unfold nb090AlphaDummy583;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0606 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy587 A) from (by
                          unfold nb090AlphaDummy587;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0608 A) 0))))
                      (show (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy588 h) from (by
                          unfold nb090AlphaDummy588;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0609 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy585 A) from (by
                            unfold nb090AlphaDummy585;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0605 A) 0))))
                        (show (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy586 h) from (by
                            unfold nb090AlphaDummy586;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0607 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy425 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy424 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090AlphaDummy428 h))).fv ∪
                      ((Class.cv (nb090AlphaDummy427 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy582 A) ≠ (nb090AlphaDummy589 A) from (by
                              unfold nb090AlphaDummy589;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0610 A) 0))))
                          (show (nb090AlphaDummy584 h) ≠ (nb090AlphaDummy591 h) from (by
                              unfold nb090AlphaDummy591;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0611 h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy582 A) ≠ (nb090AlphaDummy590 A) from (by
                                unfold nb090AlphaDummy590;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0610 A) 1))))
                            (show (nb090AlphaDummy584 h) ≠ (nb090AlphaDummy592 h) from (by
                                unfold nb090AlphaDummy592;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0611 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy582 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy584 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy596 A) from (by
          unfold nb090AlphaDummy596;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0614 A) 1)))) (show (nb090AlphaDummy591 h) ≠
        (nb090AlphaDummy599 h) from (by
          unfold nb090AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0615 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy595 A) from (by
          unfold nb090AlphaDummy595;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0614 A) 0)))) (show (nb090AlphaDummy591 h) ≠
        (nb090AlphaDummy598 h) from (by
          unfold nb090AlphaDummy598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0615 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy593 A) from (by
          unfold nb090AlphaDummy593;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0612 A)
                  0)))) (show (nb090AlphaDummy591 h) ≠ (nb090AlphaDummy594 h) from (by
          unfold nb090AlphaDummy594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0613 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy597 A), (nb090AlphaDummy600 h)), ((nb090AlphaDummy596 A),
        (nb090AlphaDummy599 h)), ((nb090AlphaDummy595 A), (nb090AlphaDummy598 h)),
        ((nb090AlphaDummy593 A), (nb090AlphaDummy594 h)), ((nb090AlphaDummy589 A),
        (nb090AlphaDummy591 h)), ((nb090AlphaDummy590 A), (nb090AlphaDummy592 h)),
        ((nb090AlphaDummy582 A), (nb090AlphaDummy584 h)), ((nb090AlphaDummy581 A),
        (nb090AlphaDummy583 h)), ((nb090AlphaDummy587 A), (nb090AlphaDummy588 h)),
        ((nb090AlphaDummy585 A), (nb090AlphaDummy586 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠ (nb090AlphaDummy603 A) from (by
          unfold
            nb090AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0618
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy604 h) from (by
          unfold
            nb090AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0619
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠
        (nb090AlphaDummy601 A) from (by
          unfold
            nb090AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0616
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy602 h) from (by
          unfold
            nb090AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0617
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy589
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠ (nb090AlphaDummy603 A) from (by
          unfold
            nb090AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0622
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy604 h) from (by
          unfold
            nb090AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0623
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠
        (nb090AlphaDummy601 A) from (by
          unfold
            nb090AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0620
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy602 h) from (by
          unfold
            nb090AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0621
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠ (nb090AlphaDummy603 A) from (by
          unfold
            nb090AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0618
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy604 h) from (by
          unfold
            nb090AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0619
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠
        (nb090AlphaDummy601 A) from (by
          unfold
            nb090AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0616
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy602 h) from (by
          unfold
            nb090AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0617
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy589
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠ (nb090AlphaDummy603 A) from (by
          unfold
            nb090AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0622
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy604 h) from (by
          unfold
            nb090AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0623
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠
        (nb090AlphaDummy601 A) from (by
          unfold
            nb090AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0620
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy602 h) from (by
          unfold
            nb090AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0621
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy597 A), (nb090AlphaDummy600 h)), ((nb090AlphaDummy596 A),
        (nb090AlphaDummy599 h)), ((nb090AlphaDummy595 A), (nb090AlphaDummy598 h)),
        ((nb090AlphaDummy593 A), (nb090AlphaDummy594 h)), ((nb090AlphaDummy589 A),
        (nb090AlphaDummy591 h)), ((nb090AlphaDummy590 A), (nb090AlphaDummy592 h)),
        ((nb090AlphaDummy582 A), (nb090AlphaDummy584 h)), ((nb090AlphaDummy581 A),
        (nb090AlphaDummy583 h)), ((nb090AlphaDummy587 A), (nb090AlphaDummy588 h)),
        ((nb090AlphaDummy585 A), (nb090AlphaDummy586 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy589 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy589 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy591 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy596
        A) ≠ (nb090AlphaDummy607 A) from (by
          unfold
            nb090AlphaDummy607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0626
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy608 h) from (by
          unfold
            nb090AlphaDummy608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0627
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠
        (nb090AlphaDummy605 A) from (by
          unfold
            nb090AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0624
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy606 h) from (by
          unfold
            nb090AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0625
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy589
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠ (nb090AlphaDummy607 A) from (by
          unfold
            nb090AlphaDummy607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0626
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy608 h) from (by
          unfold
            nb090AlphaDummy608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0627
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠
        (nb090AlphaDummy605 A) from (by
          unfold
            nb090AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0624
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy606 h) from (by
          unfold
            nb090AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0625
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy589
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy597
        A) ≠ (nb090AlphaDummy609 A) from (by
          unfold
            nb090AlphaDummy609;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0630
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy610 h) from (by
          unfold
            nb090AlphaDummy610;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0631
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠
        (nb090AlphaDummy605 A) from (by
          unfold
            nb090AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0628
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy606 h) from (by
          unfold
            nb090AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0629
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy597
        A) ≠ (nb090AlphaDummy609 A) from (by
          unfold
            nb090AlphaDummy609;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0630
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy610 h) from (by
          unfold
            nb090AlphaDummy610;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0631
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠
        (nb090AlphaDummy605 A) from (by
          unfold
            nb090AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0628
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy606 h) from (by
          unfold
            nb090AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0629
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy593 A) from
                                      (by
                                        unfold nb090AlphaDummy593;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0612 A)
                                                0)))) (show (nb090AlphaDummy591 h) ≠
                                        (nb090AlphaDummy594 h) from (by
                                        unfold nb090AlphaDummy594;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0613 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy593 A), (nb090AlphaDummy594 h)),
                                    ((nb090AlphaDummy589 A), (nb090AlphaDummy591 h)),
                                    ((nb090AlphaDummy590 A), (nb090AlphaDummy592 h)),
                                    ((nb090AlphaDummy582 A), (nb090AlphaDummy584 h)),
                                    ((nb090AlphaDummy581 A), (nb090AlphaDummy583 h)),
                                    ((nb090AlphaDummy587 A), (nb090AlphaDummy588 h)),
                                    ((nb090AlphaDummy585 A), (nb090AlphaDummy586 h)),
                                    ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                    ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                    ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                    ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy593 A) from
                                    (by
                                      unfold nb090AlphaDummy593;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0612 A)
                                              0)))) (show
                                    (nb090AlphaDummy591 h) ≠ (nb090AlphaDummy594 h) from
                                    (by
                                      unfold nb090AlphaDummy594;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0613 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy593 A) from
                                      (by
                                        unfold nb090AlphaDummy593;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0612 A)
                                                0)))) (show (nb090AlphaDummy591 h) ≠
                                        (nb090AlphaDummy594 h) from (by
                                        unfold nb090AlphaDummy594;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0613 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy593 A), (nb090AlphaDummy594 h)),
                                    ((nb090AlphaDummy589 A), (nb090AlphaDummy591 h)),
                                    ((nb090AlphaDummy590 A), (nb090AlphaDummy592 h)),
                                    ((nb090AlphaDummy582 A), (nb090AlphaDummy584 h)),
                                    ((nb090AlphaDummy581 A), (nb090AlphaDummy583 h)),
                                    ((nb090AlphaDummy587 A), (nb090AlphaDummy588 h)),
                                    ((nb090AlphaDummy585 A), (nb090AlphaDummy586 h)),
                                    ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                    ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                    ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                    ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy582 A) from (by
                        unfold nb090AlphaDummy582;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0604 A) 1))))
                    (show (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy584 h) from (by
                        unfold nb090AlphaDummy584;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0606 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy581 A) from (by
                          unfold nb090AlphaDummy581;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0604 A) 0))))
                      (show (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy583 h) from (by
                          unfold nb090AlphaDummy583;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0606 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy587 A) from (by
                            unfold nb090AlphaDummy587;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0608 A) 0))))
                        (show (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy588 h) from (by
                            unfold nb090AlphaDummy588;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0609 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy585 A) from (by
                              unfold nb090AlphaDummy585;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0605 A) 0))))
                          (show (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy586 h) from (by
                              unfold nb090AlphaDummy586;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0607 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy425 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy424 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy428 h))).fv ∪
                        ((Class.cv (nb090AlphaDummy427 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy582 A) ≠ (nb090AlphaDummy589 A) from (by
                                unfold nb090AlphaDummy589;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0610 A) 0))))
                            (show (nb090AlphaDummy584 h) ≠ (nb090AlphaDummy591 h) from (by
                                unfold nb090AlphaDummy591;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0611 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy582 A) ≠ (nb090AlphaDummy590 A) from
                                (by
                                  unfold nb090AlphaDummy590;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0610 A) 1))))
                              (show (nb090AlphaDummy584 h) ≠ (nb090AlphaDummy592 h) from
                                (by
                                  unfold nb090AlphaDummy592;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0611 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy582 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy584 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy596 A) from (by
          unfold nb090AlphaDummy596;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0614 A) 1)))) (show (nb090AlphaDummy591 h) ≠
        (nb090AlphaDummy599 h) from (by
          unfold nb090AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0615 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy595 A) from (by
          unfold nb090AlphaDummy595;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0614 A)
                  0)))) (show (nb090AlphaDummy591 h) ≠ (nb090AlphaDummy598 h) from (by
          unfold nb090AlphaDummy598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0615 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy589 A) ≠
        (nb090AlphaDummy593 A) from (by
          unfold nb090AlphaDummy593;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0612 A)
                  0)))) (show (nb090AlphaDummy591 h) ≠ (nb090AlphaDummy594 h) from (by
          unfold nb090AlphaDummy594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0613 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy597 A), (nb090AlphaDummy600 h)), ((nb090AlphaDummy596 A),
        (nb090AlphaDummy599 h)), ((nb090AlphaDummy595 A), (nb090AlphaDummy598 h)),
        ((nb090AlphaDummy593 A), (nb090AlphaDummy594 h)), ((nb090AlphaDummy589 A),
        (nb090AlphaDummy591 h)), ((nb090AlphaDummy590 A), (nb090AlphaDummy592 h)),
        ((nb090AlphaDummy582 A), (nb090AlphaDummy584 h)), ((nb090AlphaDummy581 A),
        (nb090AlphaDummy583 h)), ((nb090AlphaDummy587 A), (nb090AlphaDummy588 h)),
        ((nb090AlphaDummy585 A), (nb090AlphaDummy586 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠ (nb090AlphaDummy603 A) from (by
          unfold
            nb090AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0618
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy604 h) from (by
          unfold
            nb090AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0619
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠
        (nb090AlphaDummy601 A) from (by
          unfold
            nb090AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0616
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy602 h) from (by
          unfold
            nb090AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0617
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy589
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠ (nb090AlphaDummy603 A) from (by
          unfold
            nb090AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0622
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy604 h) from (by
          unfold
            nb090AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0623
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠
        (nb090AlphaDummy601 A) from (by
          unfold
            nb090AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0620
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy602 h) from (by
          unfold
            nb090AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0621
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠ (nb090AlphaDummy603 A) from (by
          unfold
            nb090AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0618
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy604 h) from (by
          unfold
            nb090AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0619
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠
        (nb090AlphaDummy601 A) from (by
          unfold
            nb090AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0616
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy602 h) from (by
          unfold
            nb090AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0617
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy589
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠ (nb090AlphaDummy603 A) from (by
          unfold
            nb090AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0622
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy604 h) from (by
          unfold
            nb090AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0623
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠
        (nb090AlphaDummy601 A) from (by
          unfold
            nb090AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0620
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy602 h) from (by
          unfold
            nb090AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0621
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy597 A), (nb090AlphaDummy600 h)), ((nb090AlphaDummy596 A),
        (nb090AlphaDummy599 h)), ((nb090AlphaDummy595 A), (nb090AlphaDummy598 h)),
        ((nb090AlphaDummy593 A), (nb090AlphaDummy594 h)), ((nb090AlphaDummy589 A),
        (nb090AlphaDummy591 h)), ((nb090AlphaDummy590 A), (nb090AlphaDummy592 h)),
        ((nb090AlphaDummy582 A), (nb090AlphaDummy584 h)), ((nb090AlphaDummy581 A),
        (nb090AlphaDummy583 h)), ((nb090AlphaDummy587 A), (nb090AlphaDummy588 h)),
        ((nb090AlphaDummy585 A), (nb090AlphaDummy586 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy589 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy591
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy589 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy596
        A) ≠ (nb090AlphaDummy607 A) from (by
          unfold
            nb090AlphaDummy607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0626
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy608 h) from (by
          unfold
            nb090AlphaDummy608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0627
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠
        (nb090AlphaDummy605 A) from (by
          unfold
            nb090AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0624
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy606 h) from (by
          unfold
            nb090AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0625
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy589
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠ (nb090AlphaDummy607 A) from (by
          unfold
            nb090AlphaDummy607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0626
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy608 h) from (by
          unfold
            nb090AlphaDummy608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0627
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠
        (nb090AlphaDummy605 A) from (by
          unfold
            nb090AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0624
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy606 h) from (by
          unfold
            nb090AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0625
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy589
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy597
        A) ≠ (nb090AlphaDummy609 A) from (by
          unfold
            nb090AlphaDummy609;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0630
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy610 h) from (by
          unfold
            nb090AlphaDummy610;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0631
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠
        (nb090AlphaDummy605 A) from (by
          unfold
            nb090AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0628
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy606 h) from (by
          unfold
            nb090AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0629
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy597
        A) ≠ (nb090AlphaDummy609 A) from (by
          unfold
            nb090AlphaDummy609;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0630
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy610 h) from (by
          unfold
            nb090AlphaDummy610;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0631
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠
        (nb090AlphaDummy605 A) from (by
          unfold
            nb090AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0628
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy606 h) from (by
          unfold
            nb090AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0629
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy593 A)
                                        from (by
                                          unfold nb090AlphaDummy593;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0612 A) 0)))) (show
                                        (nb090AlphaDummy591 h) ≠ (nb090AlphaDummy594 h)
                                        from (by
                                          unfold nb090AlphaDummy594;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0613 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy593 A), (nb090AlphaDummy594 h)),
                                      ((nb090AlphaDummy589 A), (nb090AlphaDummy591 h)),
                                      ((nb090AlphaDummy590 A), (nb090AlphaDummy592 h)),
                                      ((nb090AlphaDummy582 A), (nb090AlphaDummy584 h)),
                                      ((nb090AlphaDummy581 A), (nb090AlphaDummy583 h)),
                                      ((nb090AlphaDummy587 A), (nb090AlphaDummy588 h)),
                                      ((nb090AlphaDummy585 A), (nb090AlphaDummy586 h)),
                                      ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                      ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                      ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                      ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy593 A) from
                                      (by
                                        unfold nb090AlphaDummy593;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0612 A)
                                                0)))) (show (nb090AlphaDummy591 h) ≠
                                        (nb090AlphaDummy594 h) from (by
                                        unfold nb090AlphaDummy594;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0613 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy593 A)
                                        from (by
                                          unfold nb090AlphaDummy593;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0612 A) 0)))) (show
                                        (nb090AlphaDummy591 h) ≠ (nb090AlphaDummy594 h)
                                        from (by
                                          unfold nb090AlphaDummy594;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0613 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy593 A), (nb090AlphaDummy594 h)),
                                      ((nb090AlphaDummy589 A), (nb090AlphaDummy591 h)),
                                      ((nb090AlphaDummy590 A), (nb090AlphaDummy592 h)),
                                      ((nb090AlphaDummy582 A), (nb090AlphaDummy584 h)),
                                      ((nb090AlphaDummy581 A), (nb090AlphaDummy583 h)),
                                      ((nb090AlphaDummy587 A), (nb090AlphaDummy588 h)),
                                      ((nb090AlphaDummy585 A), (nb090AlphaDummy586 h)),
                                      ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                      ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                      ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                      ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part094`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0072`. -/
@[expose]
noncomputable def nb090SplitAlpha0072 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy613 A), (nb090AlphaDummy614 h)),
        ((nb090AlphaDummy582 A), (nb090AlphaDummy584 h)),
        ((nb090AlphaDummy581 A), (nb090AlphaDummy583 h)),
        ((nb090AlphaDummy611 A), (nb090AlphaDummy612 h)),
        ((nb090AlphaDummy585 A), (nb090AlphaDummy586 h)),
        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy613 A))
          (synCcompl (synCphi (Class.cv (nb090AlphaDummy582 A))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy613 A)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy614 h))
          (synCcompl (synCphi (Class.cv (nb090AlphaDummy584 h))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy614 h))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy582 A) ≠ (nb090AlphaDummy589 A) from (by
                              unfold nb090AlphaDummy589;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0610 A) 0))))
                          (show (nb090AlphaDummy584 h) ≠ (nb090AlphaDummy591 h) from (by
                              unfold nb090AlphaDummy591;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0611 h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy582 A) ≠ (nb090AlphaDummy590 A) from (by
                                unfold nb090AlphaDummy590;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0610 A) 1))))
                            (show (nb090AlphaDummy584 h) ≠ (nb090AlphaDummy592 h) from (by
                                unfold nb090AlphaDummy592;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0611 h) 1))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy582 A) ≠ (nb090AlphaDummy615 A) from
                                (by
                                  unfold nb090AlphaDummy615;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0640 A) 0))))
                              (show (nb090AlphaDummy584 h) ≠ (nb090AlphaDummy616 h) from
                                (by
                                  unfold nb090AlphaDummy616;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0641 h) 0))))
                              (TAlphaVar.there (show
                                  (nb090AlphaDummy582 A) ≠ (nb090AlphaDummy613 A) from (by
                                    unfold nb090AlphaDummy613;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0638 A)
                                            0)))) (show
                                  (nb090AlphaDummy584 h) ≠ (nb090AlphaDummy614 h) from (by
                                    unfold nb090AlphaDummy614;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0639 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy582 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy584 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy596 A) from (by
          unfold nb090AlphaDummy596;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0614 A) 1)))) (show (nb090AlphaDummy591 h) ≠
        (nb090AlphaDummy599 h) from (by
          unfold nb090AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0615 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy595 A) from (by
          unfold nb090AlphaDummy595;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0614 A) 0)))) (show (nb090AlphaDummy591 h) ≠
        (nb090AlphaDummy598 h) from (by
          unfold nb090AlphaDummy598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0615 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy593 A) from (by
          unfold nb090AlphaDummy593;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0612 A)
                  0)))) (show (nb090AlphaDummy591 h) ≠ (nb090AlphaDummy594 h) from (by
          unfold nb090AlphaDummy594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0613 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy597 A), (nb090AlphaDummy600 h)), ((nb090AlphaDummy596 A),
        (nb090AlphaDummy599 h)), ((nb090AlphaDummy595 A), (nb090AlphaDummy598 h)),
        ((nb090AlphaDummy593 A), (nb090AlphaDummy594 h)), ((nb090AlphaDummy589 A),
        (nb090AlphaDummy591 h)), ((nb090AlphaDummy590 A), (nb090AlphaDummy592 h)),
        ((nb090AlphaDummy615 A), (nb090AlphaDummy616 h)), ((nb090AlphaDummy613 A),
        (nb090AlphaDummy614 h)), ((nb090AlphaDummy582 A), (nb090AlphaDummy584 h)),
        ((nb090AlphaDummy581 A), (nb090AlphaDummy583 h)), ((nb090AlphaDummy611 A),
        (nb090AlphaDummy612 h)), ((nb090AlphaDummy585 A), (nb090AlphaDummy586 h)),
        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A),
        (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠ (nb090AlphaDummy603 A) from (by
          unfold
            nb090AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0618
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy604 h) from (by
          unfold
            nb090AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0619
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠
        (nb090AlphaDummy601 A) from (by
          unfold
            nb090AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0616
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy602 h) from (by
          unfold
            nb090AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0617
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy589
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠ (nb090AlphaDummy603 A) from (by
          unfold
            nb090AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0622
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy604 h) from (by
          unfold
            nb090AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0623
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠
        (nb090AlphaDummy601 A) from (by
          unfold
            nb090AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0620
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy602 h) from (by
          unfold
            nb090AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0621
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠ (nb090AlphaDummy603 A) from (by
          unfold
            nb090AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0618
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy604 h) from (by
          unfold
            nb090AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0619
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠
        (nb090AlphaDummy601 A) from (by
          unfold
            nb090AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0616
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy602 h) from (by
          unfold
            nb090AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0617
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy589
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠ (nb090AlphaDummy603 A) from (by
          unfold
            nb090AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0622
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy604 h) from (by
          unfold
            nb090AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0623
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠
        (nb090AlphaDummy601 A) from (by
          unfold
            nb090AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0620
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy602 h) from (by
          unfold
            nb090AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0621
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy597 A), (nb090AlphaDummy600 h)), ((nb090AlphaDummy596 A),
        (nb090AlphaDummy599 h)), ((nb090AlphaDummy595 A), (nb090AlphaDummy598 h)),
        ((nb090AlphaDummy593 A), (nb090AlphaDummy594 h)), ((nb090AlphaDummy589 A),
        (nb090AlphaDummy591 h)), ((nb090AlphaDummy590 A), (nb090AlphaDummy592 h)),
        ((nb090AlphaDummy615 A), (nb090AlphaDummy616 h)), ((nb090AlphaDummy613 A),
        (nb090AlphaDummy614 h)), ((nb090AlphaDummy582 A), (nb090AlphaDummy584 h)),
        ((nb090AlphaDummy581 A), (nb090AlphaDummy583 h)), ((nb090AlphaDummy611 A),
        (nb090AlphaDummy612 h)), ((nb090AlphaDummy585 A), (nb090AlphaDummy586 h)),
        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A),
        (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy589 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy589 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy591 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy596
        A) ≠ (nb090AlphaDummy607 A) from (by
          unfold
            nb090AlphaDummy607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0626
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy608 h) from (by
          unfold
            nb090AlphaDummy608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0627
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠
        (nb090AlphaDummy605 A) from (by
          unfold
            nb090AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0624
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy606 h) from (by
          unfold
            nb090AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0625
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy589
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠ (nb090AlphaDummy607 A) from (by
          unfold
            nb090AlphaDummy607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0626
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy608 h) from (by
          unfold
            nb090AlphaDummy608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0627
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠
        (nb090AlphaDummy605 A) from (by
          unfold
            nb090AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0624
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy606 h) from (by
          unfold
            nb090AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0625
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy589
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy597
        A) ≠ (nb090AlphaDummy609 A) from (by
          unfold
            nb090AlphaDummy609;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0630
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy610 h) from (by
          unfold
            nb090AlphaDummy610;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0631
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠
        (nb090AlphaDummy605 A) from (by
          unfold
            nb090AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0628
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy606 h) from (by
          unfold
            nb090AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0629
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy597
        A) ≠ (nb090AlphaDummy609 A) from (by
          unfold
            nb090AlphaDummy609;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0630
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy610 h) from (by
          unfold
            nb090AlphaDummy610;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0631
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠
        (nb090AlphaDummy605 A) from (by
          unfold
            nb090AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0628
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy606 h) from (by
          unfold
            nb090AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0629
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy593 A) from
                                      (by
                                        unfold nb090AlphaDummy593;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0612 A)
                                                0)))) (show (nb090AlphaDummy591 h) ≠
                                        (nb090AlphaDummy594 h) from (by
                                        unfold nb090AlphaDummy594;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0613 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy593 A), (nb090AlphaDummy594 h)),
                                    ((nb090AlphaDummy589 A), (nb090AlphaDummy591 h)),
                                    ((nb090AlphaDummy590 A), (nb090AlphaDummy592 h)),
                                    ((nb090AlphaDummy615 A), (nb090AlphaDummy616 h)),
                                    ((nb090AlphaDummy613 A), (nb090AlphaDummy614 h)),
                                    ((nb090AlphaDummy582 A), (nb090AlphaDummy584 h)),
                                    ((nb090AlphaDummy581 A), (nb090AlphaDummy583 h)),
                                    ((nb090AlphaDummy611 A), (nb090AlphaDummy612 h)),
                                    ((nb090AlphaDummy585 A), (nb090AlphaDummy586 h)),
                                    ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                    ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                    ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                    ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy593 A) from
                                    (by
                                      unfold nb090AlphaDummy593;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0612 A)
                                              0)))) (show
                                    (nb090AlphaDummy591 h) ≠ (nb090AlphaDummy594 h) from
                                    (by
                                      unfold nb090AlphaDummy594;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0613 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy593 A) from
                                      (by
                                        unfold nb090AlphaDummy593;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0612 A)
                                                0)))) (show (nb090AlphaDummy591 h) ≠
                                        (nb090AlphaDummy594 h) from (by
                                        unfold nb090AlphaDummy594;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0613 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy593 A), (nb090AlphaDummy594 h)),
                                    ((nb090AlphaDummy589 A), (nb090AlphaDummy591 h)),
                                    ((nb090AlphaDummy590 A), (nb090AlphaDummy592 h)),
                                    ((nb090AlphaDummy615 A), (nb090AlphaDummy616 h)),
                                    ((nb090AlphaDummy613 A), (nb090AlphaDummy614 h)),
                                    ((nb090AlphaDummy582 A), (nb090AlphaDummy584 h)),
                                    ((nb090AlphaDummy581 A), (nb090AlphaDummy583 h)),
                                    ((nb090AlphaDummy611 A), (nb090AlphaDummy612 h)),
                                    ((nb090AlphaDummy585 A), (nb090AlphaDummy586 h)),
                                    ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                    ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                    ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                    ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy582 A) ≠ (nb090AlphaDummy589 A) from (by
                              unfold nb090AlphaDummy589;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0610 A) 0))))
                          (show (nb090AlphaDummy584 h) ≠ (nb090AlphaDummy591 h) from (by
                              unfold nb090AlphaDummy591;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0611 h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy582 A) ≠ (nb090AlphaDummy590 A) from (by
                                unfold nb090AlphaDummy590;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0610 A) 1))))
                            (show (nb090AlphaDummy584 h) ≠ (nb090AlphaDummy592 h) from (by
                                unfold nb090AlphaDummy592;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0611 h) 1))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy582 A) ≠ (nb090AlphaDummy615 A) from
                                (by
                                  unfold nb090AlphaDummy615;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0640 A) 0))))
                              (show (nb090AlphaDummy584 h) ≠ (nb090AlphaDummy616 h) from
                                (by
                                  unfold nb090AlphaDummy616;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0641 h) 0))))
                              (TAlphaVar.there (show
                                  (nb090AlphaDummy582 A) ≠ (nb090AlphaDummy613 A) from (by
                                    unfold nb090AlphaDummy613;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0638 A)
                                            0)))) (show
                                  (nb090AlphaDummy584 h) ≠ (nb090AlphaDummy614 h) from (by
                                    unfold nb090AlphaDummy614;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0639 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy582 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy584 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy596 A) from (by
          unfold nb090AlphaDummy596;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0614 A) 1)))) (show (nb090AlphaDummy591 h) ≠
        (nb090AlphaDummy599 h) from (by
          unfold nb090AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0615 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy595 A) from (by
          unfold nb090AlphaDummy595;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0614 A) 0)))) (show (nb090AlphaDummy591 h) ≠
        (nb090AlphaDummy598 h) from (by
          unfold nb090AlphaDummy598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0615 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy593 A) from (by
          unfold nb090AlphaDummy593;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0612 A)
                  0)))) (show (nb090AlphaDummy591 h) ≠ (nb090AlphaDummy594 h) from (by
          unfold nb090AlphaDummy594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0613 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy597 A), (nb090AlphaDummy600 h)), ((nb090AlphaDummy596 A),
        (nb090AlphaDummy599 h)), ((nb090AlphaDummy595 A), (nb090AlphaDummy598 h)),
        ((nb090AlphaDummy593 A), (nb090AlphaDummy594 h)), ((nb090AlphaDummy589 A),
        (nb090AlphaDummy591 h)), ((nb090AlphaDummy590 A), (nb090AlphaDummy592 h)),
        ((nb090AlphaDummy615 A), (nb090AlphaDummy616 h)), ((nb090AlphaDummy613 A),
        (nb090AlphaDummy614 h)), ((nb090AlphaDummy582 A), (nb090AlphaDummy584 h)),
        ((nb090AlphaDummy581 A), (nb090AlphaDummy583 h)), ((nb090AlphaDummy611 A),
        (nb090AlphaDummy612 h)), ((nb090AlphaDummy585 A), (nb090AlphaDummy586 h)),
        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A),
        (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠ (nb090AlphaDummy603 A) from (by
          unfold
            nb090AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0618
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy604 h) from (by
          unfold
            nb090AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0619
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠
        (nb090AlphaDummy601 A) from (by
          unfold
            nb090AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0616
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy602 h) from (by
          unfold
            nb090AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0617
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy589
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠ (nb090AlphaDummy603 A) from (by
          unfold
            nb090AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0622
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy604 h) from (by
          unfold
            nb090AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0623
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠
        (nb090AlphaDummy601 A) from (by
          unfold
            nb090AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0620
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy602 h) from (by
          unfold
            nb090AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0621
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠ (nb090AlphaDummy603 A) from (by
          unfold
            nb090AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0618
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy604 h) from (by
          unfold
            nb090AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0619
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠
        (nb090AlphaDummy601 A) from (by
          unfold
            nb090AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0616
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy602 h) from (by
          unfold
            nb090AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0617
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy589
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠ (nb090AlphaDummy603 A) from (by
          unfold
            nb090AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0622
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy604 h) from (by
          unfold
            nb090AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0623
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠
        (nb090AlphaDummy601 A) from (by
          unfold
            nb090AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0620
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy602 h) from (by
          unfold
            nb090AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0621
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy597 A), (nb090AlphaDummy600 h)), ((nb090AlphaDummy596 A),
        (nb090AlphaDummy599 h)), ((nb090AlphaDummy595 A), (nb090AlphaDummy598 h)),
        ((nb090AlphaDummy593 A), (nb090AlphaDummy594 h)), ((nb090AlphaDummy589 A),
        (nb090AlphaDummy591 h)), ((nb090AlphaDummy590 A), (nb090AlphaDummy592 h)),
        ((nb090AlphaDummy615 A), (nb090AlphaDummy616 h)), ((nb090AlphaDummy613 A),
        (nb090AlphaDummy614 h)), ((nb090AlphaDummy582 A), (nb090AlphaDummy584 h)),
        ((nb090AlphaDummy581 A), (nb090AlphaDummy583 h)), ((nb090AlphaDummy611 A),
        (nb090AlphaDummy612 h)), ((nb090AlphaDummy585 A), (nb090AlphaDummy586 h)),
        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A),
        (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy589 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy589 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy591 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy596
        A) ≠ (nb090AlphaDummy607 A) from (by
          unfold
            nb090AlphaDummy607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0626
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy608 h) from (by
          unfold
            nb090AlphaDummy608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0627
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠
        (nb090AlphaDummy605 A) from (by
          unfold
            nb090AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0624
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy606 h) from (by
          unfold
            nb090AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0625
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy589
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠ (nb090AlphaDummy607 A) from (by
          unfold
            nb090AlphaDummy607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0626
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy608 h) from (by
          unfold
            nb090AlphaDummy608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0627
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy596 A) ≠
        (nb090AlphaDummy605 A) from (by
          unfold
            nb090AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0624
                    A)
                  0)))) (show (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy606 h) from (by
          unfold
            nb090AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0625
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy589
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy597
        A) ≠ (nb090AlphaDummy609 A) from (by
          unfold
            nb090AlphaDummy609;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0630
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy610 h) from (by
          unfold
            nb090AlphaDummy610;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0631
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠
        (nb090AlphaDummy605 A) from (by
          unfold
            nb090AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0628
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy606 h) from (by
          unfold
            nb090AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0629
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy597
        A) ≠ (nb090AlphaDummy609 A) from (by
          unfold
            nb090AlphaDummy609;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0630
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy610 h) from (by
          unfold
            nb090AlphaDummy610;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0631
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy597 A) ≠
        (nb090AlphaDummy605 A) from (by
          unfold
            nb090AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0628
                    A)
                  0)))) (show (nb090AlphaDummy600 h) ≠ (nb090AlphaDummy606 h) from (by
          unfold
            nb090AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0629
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy593 A) from
                                      (by
                                        unfold nb090AlphaDummy593;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0612 A)
                                                0)))) (show (nb090AlphaDummy591 h) ≠
                                        (nb090AlphaDummy594 h) from (by
                                        unfold nb090AlphaDummy594;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0613 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy593 A), (nb090AlphaDummy594 h)),
                                    ((nb090AlphaDummy589 A), (nb090AlphaDummy591 h)),
                                    ((nb090AlphaDummy590 A), (nb090AlphaDummy592 h)),
                                    ((nb090AlphaDummy615 A), (nb090AlphaDummy616 h)),
                                    ((nb090AlphaDummy613 A), (nb090AlphaDummy614 h)),
                                    ((nb090AlphaDummy582 A), (nb090AlphaDummy584 h)),
                                    ((nb090AlphaDummy581 A), (nb090AlphaDummy583 h)),
                                    ((nb090AlphaDummy611 A), (nb090AlphaDummy612 h)),
                                    ((nb090AlphaDummy585 A), (nb090AlphaDummy586 h)),
                                    ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                    ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                    ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                    ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy593 A) from
                                    (by
                                      unfold nb090AlphaDummy593;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0612 A)
                                              0)))) (show
                                    (nb090AlphaDummy591 h) ≠ (nb090AlphaDummy594 h) from
                                    (by
                                      unfold nb090AlphaDummy594;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0613 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy593 A) from
                                      (by
                                        unfold nb090AlphaDummy593;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0612 A)
                                                0)))) (show (nb090AlphaDummy591 h) ≠
                                        (nb090AlphaDummy594 h) from (by
                                        unfold nb090AlphaDummy594;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0613 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy593 A), (nb090AlphaDummy594 h)),
                                    ((nb090AlphaDummy589 A), (nb090AlphaDummy591 h)),
                                    ((nb090AlphaDummy590 A), (nb090AlphaDummy592 h)),
                                    ((nb090AlphaDummy615 A), (nb090AlphaDummy616 h)),
                                    ((nb090AlphaDummy613 A), (nb090AlphaDummy614 h)),
                                    ((nb090AlphaDummy582 A), (nb090AlphaDummy584 h)),
                                    ((nb090AlphaDummy581 A), (nb090AlphaDummy583 h)),
                                    ((nb090AlphaDummy611 A), (nb090AlphaDummy612 h)),
                                    ((nb090AlphaDummy585 A), (nb090AlphaDummy586 h)),
                                    ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                    ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                    ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                    ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb090AlphaDummy613 A), (nb090AlphaDummy614 h)),
            ((nb090AlphaDummy582 A), (nb090AlphaDummy584 h)),
            ((nb090AlphaDummy581 A), (nb090AlphaDummy583 h)),
            ((nb090AlphaDummy611 A), (nb090AlphaDummy612 h)),
            ((nb090AlphaDummy585 A), (nb090AlphaDummy586 h)),
            ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
            ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
            ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
            ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
            ((nb090AlphaDummy001 A), u),
            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
          (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
