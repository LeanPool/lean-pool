/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block024

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part072`. -/


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
noncomputable def nb090_split_alpha_0050 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
        ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classEq (Class.cv (nb090_alpha_dummy_507 A))
          (syn_cop (Class.cv (nb090_alpha_dummy_503 A)) (Class.cv (nb090_alpha_dummy_504 A))))
        (Wff.neg (syn_wbr (Class.cv (nb090_alpha_dummy_504 A))
            (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
            (Class.cv (nb090_alpha_dummy_503 A)))))
      (Wff.imp (Wff.classEq (Class.cv (nb090_alpha_dummy_508 h))
          (syn_cop (Class.cv (nb090_alpha_dummy_505 h)) (Class.cv (nb090_alpha_dummy_506 h))))
        (Wff.neg (syn_wbr (Class.cv (nb090_alpha_dummy_506 h)) (syn_ccnv (Class.cv h))
            (Class.cv (nb090_alpha_dummy_505 h))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_507 A) from (by
                unfold nb090_alpha_dummy_507;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0514 A) 0)))))
          (Ne.symm (show (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_508 h) from (by
                unfold nb090_alpha_dummy_508;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0515 h) 0)))))
          (TAlphaVar.there (Ne.symm
              (show (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_507 A) from (by
                  unfold nb090_alpha_dummy_507;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0512 A) 0)))))
            (Ne.symm (show (nb090_alpha_dummy_505 h) ≠ (nb090_alpha_dummy_508 h) from (by
                  unfold nb090_alpha_dummy_508;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0513 h) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0042 v u A h)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_510 A) from
                                    (by
                                      unfold nb090_alpha_dummy_510;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0544 A)
                                              1)))) (show
                                    (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_512 h) from
                                    (by
                                      unfold nb090_alpha_dummy_512;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0546 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_509 A) from
                                      (by
                                        unfold nb090_alpha_dummy_509;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0544 A)
                                                0)))) (show (nb090_alpha_dummy_506 h) ≠
                                        (nb090_alpha_dummy_511 h) from (by
                                        unfold nb090_alpha_dummy_511;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0546 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_539 A)
                                        from (by
                                          unfold nb090_alpha_dummy_539;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0548 A) 0)))) (show
                                        (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_540 h)
                                        from (by
                                          unfold nb090_alpha_dummy_540;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0549 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_504 A) ≠
        (nb090_alpha_dummy_513 A) from (by
          unfold nb090_alpha_dummy_513;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0545 A) 0)))) (show (nb090_alpha_dummy_506 h) ≠
        (nb090_alpha_dummy_514 h) from (by
          unfold nb090_alpha_dummy_514;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0547 h) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪
                                      ((Class.cv (nb090_alpha_dummy_504 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪
                                      ((Class.cv (nb090_alpha_dummy_506 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0043 v u A h))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_541 A),
        (nb090_alpha_dummy_542 h)), ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)),
        ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_539 A),
        (nb090_alpha_dummy_540 h)), ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)),
        ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A),
        (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A),
        (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A),
        (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c])))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_510 A) from
                                    (by
                                      unfold nb090_alpha_dummy_510;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0544 A)
                                              1)))) (show
                                    (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_512 h) from
                                    (by
                                      unfold nb090_alpha_dummy_512;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0546 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_509 A) from
                                      (by
                                        unfold nb090_alpha_dummy_509;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0544 A)
                                                0)))) (show (nb090_alpha_dummy_506 h) ≠
                                        (nb090_alpha_dummy_511 h) from (by
                                        unfold nb090_alpha_dummy_511;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0546 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_539 A)
                                        from (by
                                          unfold nb090_alpha_dummy_539;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0548 A) 0)))) (show
                                        (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_540 h)
                                        from (by
                                          unfold nb090_alpha_dummy_540;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0549 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_504 A) ≠
        (nb090_alpha_dummy_513 A) from (by
          unfold nb090_alpha_dummy_513;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0545 A) 0)))) (show (nb090_alpha_dummy_506 h) ≠
        (nb090_alpha_dummy_514 h) from (by
          unfold nb090_alpha_dummy_514;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0547 h) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪
                                      ((Class.cv (nb090_alpha_dummy_504 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪
                                      ((Class.cv (nb090_alpha_dummy_506 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0043 v u A h))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_541 A),
        (nb090_alpha_dummy_542 h)), ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)),
        ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_539 A),
        (nb090_alpha_dummy_540 h)), ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)),
        ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A),
        (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A),
        (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A),
        (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0044 v u A h)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_546 A) from
                                      (by
                                        unfold nb090_alpha_dummy_546;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0582 A)
                                                1)))) (show (nb090_alpha_dummy_505 h) ≠
                                        (nb090_alpha_dummy_548 h) from (by
                                        unfold nb090_alpha_dummy_548;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0584 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_545 A)
                                        from (by
                                          unfold nb090_alpha_dummy_545;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0582 A) 0)))) (show
                                        (nb090_alpha_dummy_505 h) ≠ (nb090_alpha_dummy_547 h)
                                        from (by
                                          unfold nb090_alpha_dummy_547;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0584 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_503 A) ≠
        (nb090_alpha_dummy_575 A) from (by
          unfold nb090_alpha_dummy_575;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0586 A) 0)))) (show (nb090_alpha_dummy_505 h) ≠
        (nb090_alpha_dummy_576 h) from (by
          unfold nb090_alpha_dummy_576;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0587 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_549 A) from (by
          unfold nb090_alpha_dummy_549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0583 A) 0)))) (show (nb090_alpha_dummy_505 h) ≠
        (nb090_alpha_dummy_550 h) from (by
          unfold nb090_alpha_dummy_550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0585 h) 0)))) (TAlphaVar.there (freshVar_injective
        (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) (by decide)) (freshVar_injective
        (((syn_ccnv (Class.cv h))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪
                                        ((Class.cv (nb090_alpha_dummy_503 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪
                                        ((Class.cv (nb090_alpha_dummy_505 h))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0045 v u A h))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_577 A),
        (nb090_alpha_dummy_578 h)), ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)),
        ((nb090_alpha_dummy_545 A), (nb090_alpha_dummy_547 h)), ((nb090_alpha_dummy_575 A),
        (nb090_alpha_dummy_576 h)), ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)),
        ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A),
        (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A),
        (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A),
        (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_546 A) from
                                      (by
                                        unfold nb090_alpha_dummy_546;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0582 A)
                                                1)))) (show (nb090_alpha_dummy_505 h) ≠
                                        (nb090_alpha_dummy_548 h) from (by
                                        unfold nb090_alpha_dummy_548;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0584 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_545 A)
                                        from (by
                                          unfold nb090_alpha_dummy_545;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0582 A) 0)))) (show
                                        (nb090_alpha_dummy_505 h) ≠ (nb090_alpha_dummy_547 h)
                                        from (by
                                          unfold nb090_alpha_dummy_547;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0584 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_503 A) ≠
        (nb090_alpha_dummy_575 A) from (by
          unfold nb090_alpha_dummy_575;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0586 A) 0)))) (show (nb090_alpha_dummy_505 h) ≠
        (nb090_alpha_dummy_576 h) from (by
          unfold nb090_alpha_dummy_576;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0587 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_549 A) from (by
          unfold nb090_alpha_dummy_549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0583 A) 0)))) (show (nb090_alpha_dummy_505 h) ≠
        (nb090_alpha_dummy_550 h) from (by
          unfold nb090_alpha_dummy_550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0585 h) 0)))) (TAlphaVar.there (freshVar_injective
        (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) (by decide)) (freshVar_injective
        (((syn_ccnv (Class.cv h))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪
                                        ((Class.cv (nb090_alpha_dummy_503 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪
                                        ((Class.cv (nb090_alpha_dummy_505 h))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0045 v u A h))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_577 A),
        (nb090_alpha_dummy_578 h)), ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)),
        ((nb090_alpha_dummy_545 A), (nb090_alpha_dummy_547 h)), ((nb090_alpha_dummy_575 A),
        (nb090_alpha_dummy_576 h)), ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)),
        ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A),
        (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A),
        (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A),
        (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
              (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                        (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_133 A) from (by
                            unfold nb090_alpha_dummy_133;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0124 A) 0))))) (Ne.symm
                        (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_134 h) from (by
                            unfold nb090_alpha_dummy_134;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0125 h) 0)))))
                      (TAlphaVar.there (Ne.symm
                          (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_133 A) from (by
                              unfold nb090_alpha_dummy_133;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0122 A) 0))))) (Ne.symm
                          (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_134 h) from (by
                              unfold nb090_alpha_dummy_134;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0123 h) 0)))))
                        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb090_split_alpha_0046 v u A h)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_136 A) from (by
          unfold nb090_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154 A) 1)))) (show (nb090_alpha_dummy_132 h) ≠
        (nb090_alpha_dummy_138 h) from (by
          unfold nb090_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_135 A) from (by
          unfold nb090_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154 A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_137 h) from (by
          unfold nb090_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_165 A) from (by
          unfold nb090_alpha_dummy_165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0158 A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_166 h) from (by
          unfold nb090_alpha_dummy_166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0159 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_139 A) from (by
          unfold nb090_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0155 A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_140 h) from (by
          unfold nb090_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0157 h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_130 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0047 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A),
        (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
        ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A),
        (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A),
        (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
        ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A),
        (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn, fv_syn_c0c]))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_136 A) from (by
          unfold nb090_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154 A) 1)))) (show (nb090_alpha_dummy_132 h) ≠
        (nb090_alpha_dummy_138 h) from (by
          unfold nb090_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_135 A) from (by
          unfold nb090_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154 A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_137 h) from (by
          unfold nb090_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_165 A) from (by
          unfold nb090_alpha_dummy_165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0158 A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_166 h) from (by
          unfold nb090_alpha_dummy_166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0159 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_139 A) from (by
          unfold nb090_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0155 A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_140 h) from (by
          unfold nb090_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0157 h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_130 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0047 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A),
        (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
        ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A),
        (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A),
        (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
        ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A),
        (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb090_split_alpha_0048 v u A h)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_172 A) from (by
          unfold nb090_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192 A) 1)))) (show (nb090_alpha_dummy_131 h) ≠
        (nb090_alpha_dummy_174 h) from (by
          unfold nb090_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_171 A) from (by
          unfold nb090_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192 A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_173 h) from (by
          unfold nb090_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_201 A) from (by
          unfold nb090_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0196 A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_202 h) from (by
          unfold nb090_alpha_dummy_202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0197 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_175 A) from (by
          unfold nb090_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0193 A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_176 h) from (by
          unfold nb090_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0195 h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_000
        A))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv
        (nb090_alpha_dummy_129 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0049 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A),
        (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
        ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A),
        (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A),
        (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
        ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A),
        (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn, fv_syn_c0c]))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_172 A) from (by
          unfold nb090_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192 A) 1)))) (show (nb090_alpha_dummy_131 h) ≠
        (nb090_alpha_dummy_174 h) from (by
          unfold nb090_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_171 A) from (by
          unfold nb090_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192 A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_173 h) from (by
          unfold nb090_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_201 A) from (by
          unfold nb090_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0196 A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_202 h) from (by
          unfold nb090_alpha_dummy_202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0197 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_175 A) from (by
          unfold nb090_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0193 A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_176 h) from (by
          unfold nb090_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0195 h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_000
        A))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv
        (nb090_alpha_dummy_129 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0049 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A),
        (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
        ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A),
        (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A),
        (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
        ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A),
        (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                      (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_130 A) from (by
                          unfold nb090_alpha_dummy_130;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0212 A) 1))))
                      (show h ≠ (nb090_alpha_dummy_132 h) from (by
                          unfold nb090_alpha_dummy_132;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0213 h) 1))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_129 A) from (by
                            unfold nb090_alpha_dummy_129;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0212 A) 0))))
                        (show h ≠ (nb090_alpha_dummy_131 h) from (by
                            unfold nb090_alpha_dummy_131;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0213 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_133 A) from (by
                              unfold nb090_alpha_dummy_133;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0210 A) 0))))
                          (show h ≠ (nb090_alpha_dummy_134 h) from (by
                              unfold nb090_alpha_dummy_134;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0211 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_504 A) from (by
                                unfold nb090_alpha_dummy_504;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0602 A) 1))))
                            (show h ≠ (nb090_alpha_dummy_506 h) from (by
                                unfold nb090_alpha_dummy_506;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0603 h) 1))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_503 A) from
                                (by
                                  unfold nb090_alpha_dummy_503;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0602 A) 0))))
                              (show h ≠ (nb090_alpha_dummy_505 h) from (by
                                  unfold nb090_alpha_dummy_505;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0603 h) 0))))
                              (TAlphaVar.there (show
                                  (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_507 A) from (by
                                    unfold nb090_alpha_dummy_507;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0600 A)
                                            0)))) (show h ≠ (nb090_alpha_dummy_508 h) from (by
                                    unfold nb090_alpha_dummy_508;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0601 h)
                                            0)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_425 A) from
                                    (by
                                      unfold nb090_alpha_dummy_425;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0596 A)
                                              2)))) (show h ≠ (nb090_alpha_dummy_428 h) from (by
                                      unfold nb090_alpha_dummy_428;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0598 h)
                                              2)))) (TAlphaVar.there (show
                                      (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_424 A) from
                                      (by
                                        unfold nb090_alpha_dummy_424;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0596 A)
                                                1)))) (show h ≠ (nb090_alpha_dummy_427 h) from
                                      (by
                                        unfold nb090_alpha_dummy_427;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0598 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_423 A)
                                        from (by
                                          unfold nb090_alpha_dummy_423;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0596 A) 0))))
                                      (show h ≠ (nb090_alpha_dummy_426 h) from (by
                                          unfold nb090_alpha_dummy_426;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0598 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_429 A) from (by
          unfold nb090_alpha_dummy_429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0597 A) 0)))) (show h ≠ (nb090_alpha_dummy_430 h) from (by
          unfold nb090_alpha_dummy_430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0599 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_421 A) from (by
          unfold nb090_alpha_dummy_421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0594 A) 0)))) (show h ≠ (nb090_alpha_dummy_422 h) from (by
          unfold nb090_alpha_dummy_422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0595 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_419 A) from (by
          unfold nb090_alpha_dummy_419;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0592 A) 0)))) (show h ≠ (nb090_alpha_dummy_420 h) from (by
          unfold nb090_alpha_dummy_420;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0593 h) 0)))) (TAlphaVar.here _ _ _))))))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part073`. -/


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
noncomputable def nb090_split_alpha_0051 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_587 A), (nb090_alpha_dummy_588 h)),
        ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_587 A))
          (Class.cab (nb090_alpha_dummy_581 A)
            (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_587 A))
            (Class.cab (nb090_alpha_dummy_581 A)
              (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_588 h))
          (Class.cab (nb090_alpha_dummy_583 h)
            (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_588 h))
            (Class.cab (nb090_alpha_dummy_583 h)
              (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_582 A) from (by
                      unfold nb090_alpha_dummy_582;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0604 A) 1))))
                  (show (nb090_alpha_dummy_428 h) ≠ (nb090_alpha_dummy_584 h) from (by
                      unfold nb090_alpha_dummy_584;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0606 h) 1))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_581 A) from (by
                        unfold nb090_alpha_dummy_581;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0604 A) 0))))
                    (show (nb090_alpha_dummy_428 h) ≠ (nb090_alpha_dummy_583 h) from (by
                        unfold nb090_alpha_dummy_583;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0606 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_587 A) from (by
                          unfold nb090_alpha_dummy_587;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0608 A) 0))))
                      (show (nb090_alpha_dummy_428 h) ≠ (nb090_alpha_dummy_588 h) from (by
                          unfold nb090_alpha_dummy_588;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0609 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_585 A) from (by
                            unfold nb090_alpha_dummy_585;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0605 A) 0))))
                        (show (nb090_alpha_dummy_428 h) ≠ (nb090_alpha_dummy_586 h) from (by
                            unfold nb090_alpha_dummy_586;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0607 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_424 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_427 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_582 A) ≠ (nb090_alpha_dummy_589 A) from (by
                              unfold nb090_alpha_dummy_589;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0610 A) 0))))
                          (show (nb090_alpha_dummy_584 h) ≠ (nb090_alpha_dummy_591 h) from (by
                              unfold nb090_alpha_dummy_591;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0611 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_582 A) ≠ (nb090_alpha_dummy_590 A) from (by
                                unfold nb090_alpha_dummy_590;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0610 A) 1))))
                            (show (nb090_alpha_dummy_584 h) ≠ (nb090_alpha_dummy_592 h) from (by
                                unfold nb090_alpha_dummy_592;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0611 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_582 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_584 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_596 A) from (by
          unfold nb090_alpha_dummy_596;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0614 A) 1)))) (show (nb090_alpha_dummy_591 h) ≠
        (nb090_alpha_dummy_599 h) from (by
          unfold nb090_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0615 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_595 A) from (by
          unfold nb090_alpha_dummy_595;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0614 A) 0)))) (show (nb090_alpha_dummy_591 h) ≠
        (nb090_alpha_dummy_598 h) from (by
          unfold nb090_alpha_dummy_598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0615 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_593 A) from (by
          unfold nb090_alpha_dummy_593;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0612 A)
                  0)))) (show (nb090_alpha_dummy_591 h) ≠ (nb090_alpha_dummy_594 h) from (by
          unfold nb090_alpha_dummy_594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0613 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_597 A), (nb090_alpha_dummy_600 h)), ((nb090_alpha_dummy_596 A),
        (nb090_alpha_dummy_599 h)), ((nb090_alpha_dummy_595 A), (nb090_alpha_dummy_598 h)),
        ((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)), ((nb090_alpha_dummy_589 A),
        (nb090_alpha_dummy_591 h)), ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)),
        ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)), ((nb090_alpha_dummy_581 A),
        (nb090_alpha_dummy_583 h)), ((nb090_alpha_dummy_587 A), (nb090_alpha_dummy_588 h)),
        ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠ (nb090_alpha_dummy_603 A) from (by
          unfold
            nb090_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0618
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_604 h) from (by
          unfold
            nb090_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0619
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠
        (nb090_alpha_dummy_601 A) from (by
          unfold
            nb090_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0616
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_602 h) from (by
          unfold
            nb090_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0617
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_589
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠ (nb090_alpha_dummy_603 A) from (by
          unfold
            nb090_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0622
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_604 h) from (by
          unfold
            nb090_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0623
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠
        (nb090_alpha_dummy_601 A) from (by
          unfold
            nb090_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0620
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_602 h) from (by
          unfold
            nb090_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0621
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠ (nb090_alpha_dummy_603 A) from (by
          unfold
            nb090_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0618
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_604 h) from (by
          unfold
            nb090_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0619
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠
        (nb090_alpha_dummy_601 A) from (by
          unfold
            nb090_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0616
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_602 h) from (by
          unfold
            nb090_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0617
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_589
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠ (nb090_alpha_dummy_603 A) from (by
          unfold
            nb090_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0622
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_604 h) from (by
          unfold
            nb090_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0623
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠
        (nb090_alpha_dummy_601 A) from (by
          unfold
            nb090_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0620
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_602 h) from (by
          unfold
            nb090_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0621
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_597 A), (nb090_alpha_dummy_600 h)), ((nb090_alpha_dummy_596 A),
        (nb090_alpha_dummy_599 h)), ((nb090_alpha_dummy_595 A), (nb090_alpha_dummy_598 h)),
        ((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)), ((nb090_alpha_dummy_589 A),
        (nb090_alpha_dummy_591 h)), ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)),
        ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)), ((nb090_alpha_dummy_581 A),
        (nb090_alpha_dummy_583 h)), ((nb090_alpha_dummy_587 A), (nb090_alpha_dummy_588 h)),
        ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_596
        A) ≠ (nb090_alpha_dummy_607 A) from (by
          unfold
            nb090_alpha_dummy_607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0626
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_608 h) from (by
          unfold
            nb090_alpha_dummy_608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0627
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠
        (nb090_alpha_dummy_605 A) from (by
          unfold
            nb090_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0624
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_606 h) from (by
          unfold
            nb090_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0625
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_589
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠ (nb090_alpha_dummy_607 A) from (by
          unfold
            nb090_alpha_dummy_607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0626
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_608 h) from (by
          unfold
            nb090_alpha_dummy_608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0627
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠
        (nb090_alpha_dummy_605 A) from (by
          unfold
            nb090_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0624
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_606 h) from (by
          unfold
            nb090_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0625
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_589
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_597
        A) ≠ (nb090_alpha_dummy_609 A) from (by
          unfold
            nb090_alpha_dummy_609;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0630
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_610 h) from (by
          unfold
            nb090_alpha_dummy_610;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0631
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠
        (nb090_alpha_dummy_605 A) from (by
          unfold
            nb090_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0628
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_606 h) from (by
          unfold
            nb090_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0629
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_597
        A) ≠ (nb090_alpha_dummy_609 A) from (by
          unfold
            nb090_alpha_dummy_609;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0630
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_610 h) from (by
          unfold
            nb090_alpha_dummy_610;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0631
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠
        (nb090_alpha_dummy_605 A) from (by
          unfold
            nb090_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0628
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_606 h) from (by
          unfold
            nb090_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0629
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_593 A) from
                                      (by
                                        unfold nb090_alpha_dummy_593;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0612 A)
                                                0)))) (show (nb090_alpha_dummy_591 h) ≠
                                        (nb090_alpha_dummy_594 h) from (by
                                        unfold nb090_alpha_dummy_594;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0613 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)),
                                    ((nb090_alpha_dummy_589 A), (nb090_alpha_dummy_591 h)),
                                    ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)),
                                    ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)),
                                    ((nb090_alpha_dummy_581 A), (nb090_alpha_dummy_583 h)),
                                    ((nb090_alpha_dummy_587 A), (nb090_alpha_dummy_588 h)),
                                    ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)),
                                    ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                    ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                    ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                    ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                    ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                    ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_593 A) from
                                    (by
                                      unfold nb090_alpha_dummy_593;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0612 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_591 h) ≠ (nb090_alpha_dummy_594 h) from
                                    (by
                                      unfold nb090_alpha_dummy_594;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0613 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_593 A) from
                                      (by
                                        unfold nb090_alpha_dummy_593;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0612 A)
                                                0)))) (show (nb090_alpha_dummy_591 h) ≠
                                        (nb090_alpha_dummy_594 h) from (by
                                        unfold nb090_alpha_dummy_594;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0613 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)),
                                    ((nb090_alpha_dummy_589 A), (nb090_alpha_dummy_591 h)),
                                    ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)),
                                    ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)),
                                    ((nb090_alpha_dummy_581 A), (nb090_alpha_dummy_583 h)),
                                    ((nb090_alpha_dummy_587 A), (nb090_alpha_dummy_588 h)),
                                    ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)),
                                    ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                    ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                    ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                    ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                    ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                    ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_582 A) from (by
                        unfold nb090_alpha_dummy_582;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0604 A) 1))))
                    (show (nb090_alpha_dummy_428 h) ≠ (nb090_alpha_dummy_584 h) from (by
                        unfold nb090_alpha_dummy_584;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0606 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_581 A) from (by
                          unfold nb090_alpha_dummy_581;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0604 A) 0))))
                      (show (nb090_alpha_dummy_428 h) ≠ (nb090_alpha_dummy_583 h) from (by
                          unfold nb090_alpha_dummy_583;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0606 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_587 A) from (by
                            unfold nb090_alpha_dummy_587;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0608 A) 0))))
                        (show (nb090_alpha_dummy_428 h) ≠ (nb090_alpha_dummy_588 h) from (by
                            unfold nb090_alpha_dummy_588;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0609 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_585 A) from (by
                              unfold nb090_alpha_dummy_585;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0605 A) 0))))
                          (show (nb090_alpha_dummy_428 h) ≠ (nb090_alpha_dummy_586 h) from (by
                              unfold nb090_alpha_dummy_586;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0607 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_424 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_427 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_582 A) ≠ (nb090_alpha_dummy_589 A) from (by
                                unfold nb090_alpha_dummy_589;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0610 A) 0))))
                            (show (nb090_alpha_dummy_584 h) ≠ (nb090_alpha_dummy_591 h) from (by
                                unfold nb090_alpha_dummy_591;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0611 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_582 A) ≠ (nb090_alpha_dummy_590 A) from
                                (by
                                  unfold nb090_alpha_dummy_590;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0610 A) 1))))
                              (show (nb090_alpha_dummy_584 h) ≠ (nb090_alpha_dummy_592 h) from
                                (by
                                  unfold nb090_alpha_dummy_592;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0611 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_582 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_584 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_596 A) from (by
          unfold nb090_alpha_dummy_596;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0614 A) 1)))) (show (nb090_alpha_dummy_591 h) ≠
        (nb090_alpha_dummy_599 h) from (by
          unfold nb090_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0615 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_595 A) from (by
          unfold nb090_alpha_dummy_595;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0614 A)
                  0)))) (show (nb090_alpha_dummy_591 h) ≠ (nb090_alpha_dummy_598 h) from (by
          unfold nb090_alpha_dummy_598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0615 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_589 A) ≠
        (nb090_alpha_dummy_593 A) from (by
          unfold nb090_alpha_dummy_593;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0612 A)
                  0)))) (show (nb090_alpha_dummy_591 h) ≠ (nb090_alpha_dummy_594 h) from (by
          unfold nb090_alpha_dummy_594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0613 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_597 A), (nb090_alpha_dummy_600 h)), ((nb090_alpha_dummy_596 A),
        (nb090_alpha_dummy_599 h)), ((nb090_alpha_dummy_595 A), (nb090_alpha_dummy_598 h)),
        ((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)), ((nb090_alpha_dummy_589 A),
        (nb090_alpha_dummy_591 h)), ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)),
        ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)), ((nb090_alpha_dummy_581 A),
        (nb090_alpha_dummy_583 h)), ((nb090_alpha_dummy_587 A), (nb090_alpha_dummy_588 h)),
        ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠ (nb090_alpha_dummy_603 A) from (by
          unfold
            nb090_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0618
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_604 h) from (by
          unfold
            nb090_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0619
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠
        (nb090_alpha_dummy_601 A) from (by
          unfold
            nb090_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0616
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_602 h) from (by
          unfold
            nb090_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0617
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_589
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠ (nb090_alpha_dummy_603 A) from (by
          unfold
            nb090_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0622
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_604 h) from (by
          unfold
            nb090_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0623
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠
        (nb090_alpha_dummy_601 A) from (by
          unfold
            nb090_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0620
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_602 h) from (by
          unfold
            nb090_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0621
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠ (nb090_alpha_dummy_603 A) from (by
          unfold
            nb090_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0618
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_604 h) from (by
          unfold
            nb090_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0619
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠
        (nb090_alpha_dummy_601 A) from (by
          unfold
            nb090_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0616
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_602 h) from (by
          unfold
            nb090_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0617
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_589
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠ (nb090_alpha_dummy_603 A) from (by
          unfold
            nb090_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0622
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_604 h) from (by
          unfold
            nb090_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0623
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠
        (nb090_alpha_dummy_601 A) from (by
          unfold
            nb090_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0620
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_602 h) from (by
          unfold
            nb090_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0621
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_597 A), (nb090_alpha_dummy_600 h)), ((nb090_alpha_dummy_596 A),
        (nb090_alpha_dummy_599 h)), ((nb090_alpha_dummy_595 A), (nb090_alpha_dummy_598 h)),
        ((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)), ((nb090_alpha_dummy_589 A),
        (nb090_alpha_dummy_591 h)), ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)),
        ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)), ((nb090_alpha_dummy_581 A),
        (nb090_alpha_dummy_583 h)), ((nb090_alpha_dummy_587 A), (nb090_alpha_dummy_588 h)),
        ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_591
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_596
        A) ≠ (nb090_alpha_dummy_607 A) from (by
          unfold
            nb090_alpha_dummy_607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0626
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_608 h) from (by
          unfold
            nb090_alpha_dummy_608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0627
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠
        (nb090_alpha_dummy_605 A) from (by
          unfold
            nb090_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0624
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_606 h) from (by
          unfold
            nb090_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0625
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_589
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠ (nb090_alpha_dummy_607 A) from (by
          unfold
            nb090_alpha_dummy_607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0626
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_608 h) from (by
          unfold
            nb090_alpha_dummy_608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0627
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠
        (nb090_alpha_dummy_605 A) from (by
          unfold
            nb090_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0624
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_606 h) from (by
          unfold
            nb090_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0625
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_589
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_597
        A) ≠ (nb090_alpha_dummy_609 A) from (by
          unfold
            nb090_alpha_dummy_609;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0630
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_610 h) from (by
          unfold
            nb090_alpha_dummy_610;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0631
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠
        (nb090_alpha_dummy_605 A) from (by
          unfold
            nb090_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0628
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_606 h) from (by
          unfold
            nb090_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0629
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_597
        A) ≠ (nb090_alpha_dummy_609 A) from (by
          unfold
            nb090_alpha_dummy_609;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0630
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_610 h) from (by
          unfold
            nb090_alpha_dummy_610;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0631
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠
        (nb090_alpha_dummy_605 A) from (by
          unfold
            nb090_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0628
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_606 h) from (by
          unfold
            nb090_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0629
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_593 A)
                                        from (by
                                          unfold nb090_alpha_dummy_593;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0612 A) 0)))) (show
                                        (nb090_alpha_dummy_591 h) ≠ (nb090_alpha_dummy_594 h)
                                        from (by
                                          unfold nb090_alpha_dummy_594;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0613 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)),
                                      ((nb090_alpha_dummy_589 A), (nb090_alpha_dummy_591 h)),
                                      ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)),
                                      ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)),
                                      ((nb090_alpha_dummy_581 A), (nb090_alpha_dummy_583 h)),
                                      ((nb090_alpha_dummy_587 A), (nb090_alpha_dummy_588 h)),
                                      ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)),
                                      ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                      ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                      ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                      ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                      ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                      ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_593 A) from
                                      (by
                                        unfold nb090_alpha_dummy_593;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0612 A)
                                                0)))) (show (nb090_alpha_dummy_591 h) ≠
                                        (nb090_alpha_dummy_594 h) from (by
                                        unfold nb090_alpha_dummy_594;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0613 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_593 A)
                                        from (by
                                          unfold nb090_alpha_dummy_593;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0612 A) 0)))) (show
                                        (nb090_alpha_dummy_591 h) ≠ (nb090_alpha_dummy_594 h)
                                        from (by
                                          unfold nb090_alpha_dummy_594;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0613 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)),
                                      ((nb090_alpha_dummy_589 A), (nb090_alpha_dummy_591 h)),
                                      ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)),
                                      ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)),
                                      ((nb090_alpha_dummy_581 A), (nb090_alpha_dummy_583 h)),
                                      ((nb090_alpha_dummy_587 A), (nb090_alpha_dummy_588 h)),
                                      ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)),
                                      ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                      ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                      ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                      ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                      ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                      ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part074`. -/


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
noncomputable def nb090_split_alpha_0052 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_615 A), (nb090_alpha_dummy_616 h)),
        ((nb090_alpha_dummy_613 A), (nb090_alpha_dummy_614 h)),
        ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)),
        ((nb090_alpha_dummy_581 A), (nb090_alpha_dummy_583 h)),
        ((nb090_alpha_dummy_611 A), (nb090_alpha_dummy_612 h)),
        ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_615 A))
          (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_615 A))
            (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_616 h))
          (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_616 h))
            (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_582 A) ≠ (nb090_alpha_dummy_589 A) from (by
                      unfold nb090_alpha_dummy_589;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0610 A) 0))))
                  (show (nb090_alpha_dummy_584 h) ≠ (nb090_alpha_dummy_591 h) from (by
                      unfold nb090_alpha_dummy_591;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0611 h) 0))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_582 A) ≠ (nb090_alpha_dummy_590 A) from (by
                        unfold nb090_alpha_dummy_590;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0610 A) 1))))
                    (show (nb090_alpha_dummy_584 h) ≠ (nb090_alpha_dummy_592 h) from (by
                        unfold nb090_alpha_dummy_592;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0611 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_582 A) ≠ (nb090_alpha_dummy_615 A) from (by
                          unfold nb090_alpha_dummy_615;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0640 A) 0))))
                      (show (nb090_alpha_dummy_584 h) ≠ (nb090_alpha_dummy_616 h) from (by
                          unfold nb090_alpha_dummy_616;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0641 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_582 A) ≠ (nb090_alpha_dummy_613 A) from (by
                            unfold nb090_alpha_dummy_613;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0638 A) 0))))
                        (show (nb090_alpha_dummy_584 h) ≠ (nb090_alpha_dummy_614 h) from (by
                            unfold nb090_alpha_dummy_614;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0639 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_582 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_584 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_596 A) from
                                      (by
                                        unfold nb090_alpha_dummy_596;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0614 A)
                                                1)))) (show (nb090_alpha_dummy_591 h) ≠
                                        (nb090_alpha_dummy_599 h) from (by
                                        unfold nb090_alpha_dummy_599;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0615 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_595 A)
                                        from (by
                                          unfold nb090_alpha_dummy_595;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0614 A) 0)))) (show
                                        (nb090_alpha_dummy_591 h) ≠ (nb090_alpha_dummy_598 h)
                                        from (by
                                          unfold nb090_alpha_dummy_598;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0615 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_589 A) ≠
        (nb090_alpha_dummy_593 A) from (by
          unfold nb090_alpha_dummy_593;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0612 A) 0)))) (show (nb090_alpha_dummy_591 h) ≠
        (nb090_alpha_dummy_594 h) from (by
          unfold nb090_alpha_dummy_594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0613 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_597 A),
        (nb090_alpha_dummy_600 h)), ((nb090_alpha_dummy_596 A), (nb090_alpha_dummy_599 h)),
                                        ((nb090_alpha_dummy_595 A), (nb090_alpha_dummy_598 h)),
                                        ((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)),
                                        ((nb090_alpha_dummy_589 A), (nb090_alpha_dummy_591 h)),
                                        ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)),
                                        ((nb090_alpha_dummy_615 A), (nb090_alpha_dummy_616 h)),
                                        ((nb090_alpha_dummy_613 A), (nb090_alpha_dummy_614 h)),
                                        ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)),
                                        ((nb090_alpha_dummy_581 A), (nb090_alpha_dummy_583 h)),
                                        ((nb090_alpha_dummy_611 A), (nb090_alpha_dummy_612 h)),
                                        ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)),
                                        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                        ((nb090_alpha_dummy_000 A), h),
                                        ((nb090_alpha_dummy_002 A), v),
                                        ((nb090_alpha_dummy_001 A), u),
                                        ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠ (nb090_alpha_dummy_603 A) from (by
          unfold
            nb090_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0618
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_604 h) from (by
          unfold
            nb090_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0619
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠
        (nb090_alpha_dummy_601 A) from (by
          unfold
            nb090_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0616
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_602 h) from (by
          unfold
            nb090_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0617
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_589
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠
        (nb090_alpha_dummy_603 A) from (by
          unfold
            nb090_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0622
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_604 h) from (by
          unfold
            nb090_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0623
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠
        (nb090_alpha_dummy_601 A) from (by
          unfold
            nb090_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0620
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_602 h) from (by
          unfold
            nb090_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0621
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠ (nb090_alpha_dummy_603 A) from (by
          unfold
            nb090_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0618
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_604 h) from (by
          unfold
            nb090_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0619
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠
        (nb090_alpha_dummy_601 A) from (by
          unfold
            nb090_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0616
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_602 h) from (by
          unfold
            nb090_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0617
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_589
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠
        (nb090_alpha_dummy_603 A) from (by
          unfold
            nb090_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0622
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_604 h) from (by
          unfold
            nb090_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0623
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠
        (nb090_alpha_dummy_601 A) from (by
          unfold
            nb090_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0620
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_602 h) from (by
          unfold
            nb090_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0621
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb090_alpha_dummy_597 A), (nb090_alpha_dummy_600 h)),
        ((nb090_alpha_dummy_596 A), (nb090_alpha_dummy_599 h)), ((nb090_alpha_dummy_595 A),
        (nb090_alpha_dummy_598 h)), ((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)),
        ((nb090_alpha_dummy_589 A), (nb090_alpha_dummy_591 h)), ((nb090_alpha_dummy_590 A),
        (nb090_alpha_dummy_592 h)), ((nb090_alpha_dummy_615 A), (nb090_alpha_dummy_616 h)),
        ((nb090_alpha_dummy_613 A), (nb090_alpha_dummy_614 h)), ((nb090_alpha_dummy_582 A),
        (nb090_alpha_dummy_584 h)), ((nb090_alpha_dummy_581 A), (nb090_alpha_dummy_583 h)),
        ((nb090_alpha_dummy_611 A), (nb090_alpha_dummy_612 h)), ((nb090_alpha_dummy_585 A),
        (nb090_alpha_dummy_586 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_596 A) ≠ (nb090_alpha_dummy_607 A) from (by
          unfold
            nb090_alpha_dummy_607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0626
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_608 h) from (by
          unfold
            nb090_alpha_dummy_608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0627
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠
        (nb090_alpha_dummy_605 A) from (by
          unfold
            nb090_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0624
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_606 h) from (by
          unfold
            nb090_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0625
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_589
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠
        (nb090_alpha_dummy_607 A) from (by
          unfold
            nb090_alpha_dummy_607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0626
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_608 h) from (by
          unfold
            nb090_alpha_dummy_608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0627
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠
        (nb090_alpha_dummy_605 A) from (by
          unfold
            nb090_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0624
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_606 h) from (by
          unfold
            nb090_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0625
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_589
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_597 A) ≠ (nb090_alpha_dummy_609 A) from (by
          unfold
            nb090_alpha_dummy_609;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0630
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_610 h) from (by
          unfold
            nb090_alpha_dummy_610;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0631
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠
        (nb090_alpha_dummy_605 A) from (by
          unfold
            nb090_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0628
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_606 h) from (by
          unfold
            nb090_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0629
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_597 A) ≠ (nb090_alpha_dummy_609 A) from (by
          unfold
            nb090_alpha_dummy_609;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0630
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_610 h) from (by
          unfold
            nb090_alpha_dummy_610;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0631
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠
        (nb090_alpha_dummy_605 A) from (by
          unfold
            nb090_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0628
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_606 h) from (by
          unfold
            nb090_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0629
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_593 A) from (by
                                unfold nb090_alpha_dummy_593;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0612 A) 0))))
                            (show (nb090_alpha_dummy_591 h) ≠ (nb090_alpha_dummy_594 h) from (by
                                unfold nb090_alpha_dummy_594;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0613 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)),
                            ((nb090_alpha_dummy_589 A), (nb090_alpha_dummy_591 h)),
                            ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)),
                            ((nb090_alpha_dummy_615 A), (nb090_alpha_dummy_616 h)),
                            ((nb090_alpha_dummy_613 A), (nb090_alpha_dummy_614 h)),
                            ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)),
                            ((nb090_alpha_dummy_581 A), (nb090_alpha_dummy_583 h)),
                            ((nb090_alpha_dummy_611 A), (nb090_alpha_dummy_612 h)),
                            ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)),
                            ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                            ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                            ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                            ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                            ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                            ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_593 A) from (by
                              unfold nb090_alpha_dummy_593;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0612 A) 0))))
                          (show (nb090_alpha_dummy_591 h) ≠ (nb090_alpha_dummy_594 h) from (by
                              unfold nb090_alpha_dummy_594;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0613 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_593 A) from (by
                                unfold nb090_alpha_dummy_593;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0612 A) 0))))
                            (show (nb090_alpha_dummy_591 h) ≠ (nb090_alpha_dummy_594 h) from (by
                                unfold nb090_alpha_dummy_594;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0613 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)),
                            ((nb090_alpha_dummy_589 A), (nb090_alpha_dummy_591 h)),
                            ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)),
                            ((nb090_alpha_dummy_615 A), (nb090_alpha_dummy_616 h)),
                            ((nb090_alpha_dummy_613 A), (nb090_alpha_dummy_614 h)),
                            ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)),
                            ((nb090_alpha_dummy_581 A), (nb090_alpha_dummy_583 h)),
                            ((nb090_alpha_dummy_611 A), (nb090_alpha_dummy_612 h)),
                            ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)),
                            ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                            ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                            ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                            ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                            ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                            ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090_alpha_dummy_582 A) ≠ (nb090_alpha_dummy_589 A) from (by
                        unfold nb090_alpha_dummy_589;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0610 A) 0))))
                    (show (nb090_alpha_dummy_584 h) ≠ (nb090_alpha_dummy_591 h) from (by
                        unfold nb090_alpha_dummy_591;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0611 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_582 A) ≠ (nb090_alpha_dummy_590 A) from (by
                          unfold nb090_alpha_dummy_590;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0610 A) 1))))
                      (show (nb090_alpha_dummy_584 h) ≠ (nb090_alpha_dummy_592 h) from (by
                          unfold nb090_alpha_dummy_592;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0611 h) 1))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_582 A) ≠ (nb090_alpha_dummy_615 A) from (by
                            unfold nb090_alpha_dummy_615;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0640 A) 0))))
                        (show (nb090_alpha_dummy_584 h) ≠ (nb090_alpha_dummy_616 h) from (by
                            unfold nb090_alpha_dummy_616;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0641 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_582 A) ≠ (nb090_alpha_dummy_613 A) from (by
                              unfold nb090_alpha_dummy_613;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0638 A) 0))))
                          (show (nb090_alpha_dummy_584 h) ≠ (nb090_alpha_dummy_614 h) from (by
                              unfold nb090_alpha_dummy_614;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0639 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_582 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_584 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090_alpha_dummy_589 A) ≠
        (nb090_alpha_dummy_596 A) from (by
                                          unfold nb090_alpha_dummy_596;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0614 A) 1)))) (show
                                        (nb090_alpha_dummy_591 h) ≠ (nb090_alpha_dummy_599 h)
                                        from (by
                                          unfold nb090_alpha_dummy_599;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0615 h) 1))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_589 A) ≠
        (nb090_alpha_dummy_595 A) from (by
          unfold nb090_alpha_dummy_595;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0614 A) 0)))) (show (nb090_alpha_dummy_591 h) ≠
        (nb090_alpha_dummy_598 h) from (by
          unfold nb090_alpha_dummy_598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0615 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_593 A) from (by
          unfold nb090_alpha_dummy_593;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0612 A) 0)))) (show (nb090_alpha_dummy_591 h) ≠
        (nb090_alpha_dummy_594 h) from (by
          unfold nb090_alpha_dummy_594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0613 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_597 A),
        (nb090_alpha_dummy_600 h)), ((nb090_alpha_dummy_596 A), (nb090_alpha_dummy_599 h)),
        ((nb090_alpha_dummy_595 A), (nb090_alpha_dummy_598 h)), ((nb090_alpha_dummy_593 A),
        (nb090_alpha_dummy_594 h)), ((nb090_alpha_dummy_589 A), (nb090_alpha_dummy_591 h)),
        ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)), ((nb090_alpha_dummy_615 A),
        (nb090_alpha_dummy_616 h)), ((nb090_alpha_dummy_613 A), (nb090_alpha_dummy_614 h)),
        ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)), ((nb090_alpha_dummy_581 A),
        (nb090_alpha_dummy_583 h)), ((nb090_alpha_dummy_611 A), (nb090_alpha_dummy_612 h)),
        ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_596 A) ≠ (nb090_alpha_dummy_603 A) from (by
          unfold
            nb090_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0618
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_604 h) from (by
          unfold
            nb090_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0619
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠
        (nb090_alpha_dummy_601 A) from (by
          unfold
            nb090_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0616
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_602 h) from (by
          unfold
            nb090_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0617
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_589
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠ (nb090_alpha_dummy_603 A) from (by
          unfold
            nb090_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0622
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_604 h) from (by
          unfold
            nb090_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0623
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠
        (nb090_alpha_dummy_601 A) from (by
          unfold
            nb090_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0620
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_602 h) from (by
          unfold
            nb090_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0621
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠ (nb090_alpha_dummy_603 A) from (by
          unfold
            nb090_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0618
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_604 h) from (by
          unfold
            nb090_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0619
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠
        (nb090_alpha_dummy_601 A) from (by
          unfold
            nb090_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0616
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_602 h) from (by
          unfold
            nb090_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0617
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_589
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠ (nb090_alpha_dummy_603 A) from (by
          unfold
            nb090_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0622
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_604 h) from (by
          unfold
            nb090_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0623
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠
        (nb090_alpha_dummy_601 A) from (by
          unfold
            nb090_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0620
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_602 h) from (by
          unfold
            nb090_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0621
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_597 A), (nb090_alpha_dummy_600 h)), ((nb090_alpha_dummy_596 A),
        (nb090_alpha_dummy_599 h)), ((nb090_alpha_dummy_595 A), (nb090_alpha_dummy_598 h)),
        ((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)), ((nb090_alpha_dummy_589 A),
        (nb090_alpha_dummy_591 h)), ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)),
        ((nb090_alpha_dummy_615 A), (nb090_alpha_dummy_616 h)), ((nb090_alpha_dummy_613 A),
        (nb090_alpha_dummy_614 h)), ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)),
        ((nb090_alpha_dummy_581 A), (nb090_alpha_dummy_583 h)), ((nb090_alpha_dummy_611 A),
        (nb090_alpha_dummy_612 h)), ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A),
        (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A),
        (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_596 A) ≠ (nb090_alpha_dummy_607 A) from (by
          unfold
            nb090_alpha_dummy_607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0626
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_608 h) from (by
          unfold
            nb090_alpha_dummy_608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0627
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠
        (nb090_alpha_dummy_605 A) from (by
          unfold
            nb090_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0624
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_606 h) from (by
          unfold
            nb090_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0625
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_589
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠ (nb090_alpha_dummy_607 A) from (by
          unfold
            nb090_alpha_dummy_607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0626
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_608 h) from (by
          unfold
            nb090_alpha_dummy_608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0627
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_596 A) ≠
        (nb090_alpha_dummy_605 A) from (by
          unfold
            nb090_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0624
                    A)
                  0)))) (show (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_606 h) from (by
          unfold
            nb090_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0625
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_589
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_597 A) ≠ (nb090_alpha_dummy_609 A) from (by
          unfold
            nb090_alpha_dummy_609;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0630
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_610 h) from (by
          unfold
            nb090_alpha_dummy_610;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0631
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠
        (nb090_alpha_dummy_605 A) from (by
          unfold
            nb090_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0628
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_606 h) from (by
          unfold
            nb090_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0629
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_597 A) ≠ (nb090_alpha_dummy_609 A) from (by
          unfold
            nb090_alpha_dummy_609;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0630
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_610 h) from (by
          unfold
            nb090_alpha_dummy_610;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0631
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_597 A) ≠
        (nb090_alpha_dummy_605 A) from (by
          unfold
            nb090_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0628
                    A)
                  0)))) (show (nb090_alpha_dummy_600 h) ≠ (nb090_alpha_dummy_606 h) from (by
          unfold
            nb090_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0629
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_593 A) from
                                (by
                                  unfold nb090_alpha_dummy_593;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0612 A) 0))))
                              (show (nb090_alpha_dummy_591 h) ≠ (nb090_alpha_dummy_594 h) from
                                (by
                                  unfold nb090_alpha_dummy_594;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0613 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)),
                              ((nb090_alpha_dummy_589 A), (nb090_alpha_dummy_591 h)),
                              ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)),
                              ((nb090_alpha_dummy_615 A), (nb090_alpha_dummy_616 h)),
                              ((nb090_alpha_dummy_613 A), (nb090_alpha_dummy_614 h)),
                              ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)),
                              ((nb090_alpha_dummy_581 A), (nb090_alpha_dummy_583 h)),
                              ((nb090_alpha_dummy_611 A), (nb090_alpha_dummy_612 h)),
                              ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)),
                              ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                              ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                              ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                              ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                              ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                              ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_593 A) from (by
                                unfold nb090_alpha_dummy_593;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0612 A) 0))))
                            (show (nb090_alpha_dummy_591 h) ≠ (nb090_alpha_dummy_594 h) from (by
                                unfold nb090_alpha_dummy_594;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0613 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_593 A) from
                                (by
                                  unfold nb090_alpha_dummy_593;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0612 A) 0))))
                              (show (nb090_alpha_dummy_591 h) ≠ (nb090_alpha_dummy_594 h) from
                                (by
                                  unfold nb090_alpha_dummy_594;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0613 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)),
                              ((nb090_alpha_dummy_589 A), (nb090_alpha_dummy_591 h)),
                              ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)),
                              ((nb090_alpha_dummy_615 A), (nb090_alpha_dummy_616 h)),
                              ((nb090_alpha_dummy_613 A), (nb090_alpha_dummy_614 h)),
                              ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)),
                              ((nb090_alpha_dummy_581 A), (nb090_alpha_dummy_583 h)),
                              ((nb090_alpha_dummy_611 A), (nb090_alpha_dummy_612 h)),
                              ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)),
                              ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                              ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                              ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                              ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                              ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                              ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
