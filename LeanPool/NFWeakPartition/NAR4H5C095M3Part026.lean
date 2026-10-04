/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part025

/-! NF weak partition development: NAR4H5C095M3Part026. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0049`. -/
@[expose]
noncomputable def nb095SplitAlpha0049 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_f_u : f ≠ u) (dv_f_x : f ≠ x) :
    TAlphaWff
      [((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
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
      (Wff.imp (Wff.classEq (Class.cv (nb095AlphaDummy469 D R S_cls E))
          (synCop (Class.cv (nb095AlphaDummy465 D R S_cls E))
            (Class.cv (nb095AlphaDummy466 D R S_cls E)))) (Wff.neg
          (synWbr (Class.cv (nb095AlphaDummy466 D R S_cls E))
            (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
            (Class.cv (nb095AlphaDummy465 D R S_cls E)))))
      (Wff.imp (Wff.classEq (Class.cv (nb095AlphaDummy470 f))
          (synCop (Class.cv (nb095AlphaDummy467 f)) (Class.cv (nb095AlphaDummy468 f))))
        (Wff.neg (synWbr (Class.cv (nb095AlphaDummy468 f)) (synCcnv (Class.cv f))
            (Class.cv (nb095AlphaDummy467 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
              (nb095AlphaDummy466 D R S_cls E) ≠ (nb095AlphaDummy469 D R S_cls E) from (by
                unfold nb095AlphaDummy469;
                with_reducible
                  exact
                    (Nat.ne_of_lt
                      (mem_lt_freshVar (nb095_support_mem_0472 D R S_cls E) 0))))) (Ne.symm
            (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy470 f) from (by
                unfold nb095AlphaDummy470;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0473 f) 0)))))
          (TAlphaVar.there (Ne.symm (show
                (nb095AlphaDummy465 D R S_cls E) ≠ (nb095AlphaDummy469 D R S_cls E) from
                (by
                  unfold nb095AlphaDummy469;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb095_support_mem_0470 D R S_cls E) 0))))) (Ne.symm
              (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy470 f) from (by
                  unfold nb095AlphaDummy470;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0471 f) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0041 x u D R S_cls f E)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy466 D R S_cls E) ≠
                                      (nb095AlphaDummy472 D R S_cls E) from (by
                                      unfold nb095AlphaDummy472;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0502 D R S_cls E) 1)))) (show
                                    (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy474 f) from
                                    (by
                                      unfold nb095AlphaDummy474;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0504 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy466 D R S_cls E) ≠
                                        (nb095AlphaDummy471 D R S_cls E) from (by
                                        unfold nb095AlphaDummy471;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0502 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy473 f) from
                                      (by
                                        unfold nb095AlphaDummy473;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0504 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy466 D R S_cls E) ≠
        (nb095AlphaDummy501 D R S_cls E) from (by
                                          unfold nb095AlphaDummy501;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0506 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy468 f) ≠
        (nb095AlphaDummy502 f) from (by
                                          unfold nb095AlphaDummy502;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0507 f) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy466 D R S_cls E) ≠ (nb095AlphaDummy475 D R S_cls E) from (by
          unfold nb095AlphaDummy475;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0503 D R S_cls E)
                  0)))) (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy476 f) from (by
          unfold nb095AlphaDummy476;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0505 f) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv ∪
                                      ((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv (nb095AlphaDummy467 f))).fv ∪
                                      ((Class.cv (nb095AlphaDummy468 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0042 x u D R S_cls f E))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [((nb095AlphaDummy503 D R S_cls E),
        (nb095AlphaDummy504 f)), ((nb095AlphaDummy472 D R S_cls E),
        (nb095AlphaDummy474 f)), ((nb095AlphaDummy471 D R S_cls E),
        (nb095AlphaDummy473 f)), ((nb095AlphaDummy501 D R S_cls E),
        (nb095AlphaDummy502 f)), ((nb095AlphaDummy475 D R S_cls E),
        (nb095AlphaDummy476 f)), ((nb095AlphaDummy466 D R S_cls E),
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
                                        (synCcompl (synCsn (synC0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c])))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy466 D R S_cls E) ≠
                                      (nb095AlphaDummy472 D R S_cls E) from (by
                                      unfold nb095AlphaDummy472;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0502 D R S_cls E) 1)))) (show
                                    (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy474 f) from
                                    (by
                                      unfold nb095AlphaDummy474;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0504 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy466 D R S_cls E) ≠
                                        (nb095AlphaDummy471 D R S_cls E) from (by
                                        unfold nb095AlphaDummy471;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0502 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy473 f) from
                                      (by
                                        unfold nb095AlphaDummy473;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0504 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy466 D R S_cls E) ≠
        (nb095AlphaDummy501 D R S_cls E) from (by
                                          unfold nb095AlphaDummy501;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0506 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy468 f) ≠
        (nb095AlphaDummy502 f) from (by
                                          unfold nb095AlphaDummy502;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0507 f) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy466 D R S_cls E) ≠ (nb095AlphaDummy475 D R S_cls E) from (by
          unfold nb095AlphaDummy475;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0503 D R S_cls E)
                  0)))) (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy476 f) from (by
          unfold nb095AlphaDummy476;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0505 f) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv ∪
                                      ((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv (nb095AlphaDummy467 f))).fv ∪
                                      ((Class.cv (nb095AlphaDummy468 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0042 x u D R S_cls f E))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [((nb095AlphaDummy503 D R S_cls E),
        (nb095AlphaDummy504 f)), ((nb095AlphaDummy472 D R S_cls E),
        (nb095AlphaDummy474 f)), ((nb095AlphaDummy471 D R S_cls E),
        (nb095AlphaDummy473 f)), ((nb095AlphaDummy501 D R S_cls E),
        (nb095AlphaDummy502 f)), ((nb095AlphaDummy475 D R S_cls E),
        (nb095AlphaDummy476 f)), ((nb095AlphaDummy466 D R S_cls E),
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
                                        (synCcompl (synCsn (synC0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0043 x u D R S_cls f E)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy465 D R S_cls E) ≠
                                        (nb095AlphaDummy508 D R S_cls E) from (by
                                        unfold nb095AlphaDummy508;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0540 D R S_cls E) 1)))) (show
                                      (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy510 f) from
                                      (by
                                        unfold nb095AlphaDummy510;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0542 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy465 D R S_cls E) ≠
        (nb095AlphaDummy507 D R S_cls E) from (by
                                          unfold nb095AlphaDummy507;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0540 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy467 f) ≠
        (nb095AlphaDummy509 f) from (by
                                          unfold nb095AlphaDummy509;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0542 f) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy465 D R S_cls E) ≠ (nb095AlphaDummy537 D R S_cls E) from (by
          unfold nb095AlphaDummy537;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0544 D R S_cls E)
                  0)))) (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy538 f) from (by
          unfold nb095AlphaDummy538;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0545 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy465 D R S_cls E) ≠ (nb095AlphaDummy511 D R S_cls E) from (by
          unfold nb095AlphaDummy511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0541 D R S_cls E)
                  0)))) (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy512 f) from (by
          unfold nb095AlphaDummy512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0543 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv) (by decide))
        (freshVar_injective (((synCcnv (Class.cv f))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective (((Class.cv
        (nb095AlphaDummy466 D R S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy465 D R S_cls E))).fv) (by decide)) (freshVar_injective
                                      (((Class.cv (nb095AlphaDummy468 f))).fv ∪
                                        ((Class.cv (nb095AlphaDummy467 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0044 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy539 D R S_cls E), (nb095AlphaDummy540 f)),
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
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy465 D R S_cls E) ≠
                                        (nb095AlphaDummy508 D R S_cls E) from (by
                                        unfold nb095AlphaDummy508;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0540 D R S_cls E) 1)))) (show
                                      (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy510 f) from
                                      (by
                                        unfold nb095AlphaDummy510;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0542 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy465 D R S_cls E) ≠
        (nb095AlphaDummy507 D R S_cls E) from (by
                                          unfold nb095AlphaDummy507;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0540 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy467 f) ≠
        (nb095AlphaDummy509 f) from (by
                                          unfold nb095AlphaDummy509;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0542 f) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy465 D R S_cls E) ≠ (nb095AlphaDummy537 D R S_cls E) from (by
          unfold nb095AlphaDummy537;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0544 D R S_cls E)
                  0)))) (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy538 f) from (by
          unfold nb095AlphaDummy538;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0545 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy465 D R S_cls E) ≠ (nb095AlphaDummy511 D R S_cls E) from (by
          unfold nb095AlphaDummy511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0541 D R S_cls E)
                  0)))) (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy512 f) from (by
          unfold nb095AlphaDummy512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0543 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv) (by decide))
        (freshVar_injective (((synCcnv (Class.cv f))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective (((Class.cv
        (nb095AlphaDummy466 D R S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy465 D R S_cls E))).fv) (by decide)) (freshVar_injective
                                      (((Class.cv (nb095AlphaDummy468 f))).fv ∪
                                        ((Class.cv (nb095AlphaDummy467 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0044 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy539 D R S_cls E), (nb095AlphaDummy540 f)),
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
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
              (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                          (nb095AlphaDummy092 D R S_cls E) ≠
                            (nb095AlphaDummy095 D R S_cls E) from (by
                            unfold nb095AlphaDummy095;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0082 D R S_cls E)
                                    0))))) (Ne.symm
                        (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy096 f) from (by
                            unfold nb095AlphaDummy096;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0083 f) 0)))))
                      (TAlphaVar.there (Ne.symm (show (nb095AlphaDummy091 D R S_cls E) ≠
                              (nb095AlphaDummy095 D R S_cls E) from (by
                              unfold nb095AlphaDummy095;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0080 D R S_cls E)
                                      0))))) (Ne.symm
                          (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy096 f) from (by
                              unfold nb095AlphaDummy096;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0081 f) 0)))))
                        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                (nb095SplitAlpha0045 x u D R S_cls f E)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy092 D R S_cls E) ≠ (nb095AlphaDummy098 D R S_cls E) from (by
          unfold nb095AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy100 f) from (by
          unfold nb095AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy092 D R S_cls E) ≠ (nb095AlphaDummy097 D R S_cls E) from (by
          unfold nb095AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy099 f) from (by
          unfold nb095AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy127 D R S_cls E) from (by
          unfold nb095AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0116 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy128 f) from (by
          unfold nb095AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0117 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy101 D R S_cls E) from (by
          unfold nb095AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0113 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy102 f) from (by
          unfold nb095AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0115 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy091 D R S_cls
        E))).fv ∪ ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪ ((Class.cv
        (nb095AlphaDummy094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0046 x u D R S_cls f E))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy129 D R S_cls E), (nb095AlphaDummy130 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy127 D R S_cls E), (nb095AlphaDummy128 f)),
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
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn, fv_syn_c0c]))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy092 D R S_cls E) ≠ (nb095AlphaDummy098 D R S_cls E) from (by
          unfold nb095AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy100 f) from (by
          unfold nb095AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy092 D R S_cls E) ≠ (nb095AlphaDummy097 D R S_cls E) from (by
          unfold nb095AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy099 f) from (by
          unfold nb095AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy127 D R S_cls E) from (by
          unfold nb095AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0116 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy128 f) from (by
          unfold nb095AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0117 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy101 D R S_cls E) from (by
          unfold nb095AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0113 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy102 f) from (by
          unfold nb095AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0115 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy091 D R S_cls
        E))).fv ∪ ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪ ((Class.cv
        (nb095AlphaDummy094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0046 x u D R S_cls f E))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy129 D R S_cls E), (nb095AlphaDummy130 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy127 D R S_cls E), (nb095AlphaDummy128 f)),
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
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                (nb095SplitAlpha0047 x u D R S_cls f E)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy091 D R S_cls E) ≠ (nb095AlphaDummy134 D R S_cls E) from (by
          unfold nb095AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy136 f) from (by
          unfold nb095AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy091 D R S_cls E) ≠ (nb095AlphaDummy133 D R S_cls E) from (by
          unfold nb095AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy135 f) from (by
          unfold nb095AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy163 D R S_cls E) from (by
          unfold nb095AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0154 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy164 f) from (by
          unfold nb095AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0155 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy137 D R S_cls E) from (by
          unfold nb095AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0151 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy138 f) from (by
          unfold nb095AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0153 f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy000 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy092 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy091 D R S_cls
        E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy094 f))).fv ∪
        ((Class.cv (nb095AlphaDummy093 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0048 x u D R S_cls f E))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy165 D R S_cls E), (nb095AlphaDummy166 f)),
        ((nb095AlphaDummy134 D R S_cls E), (nb095AlphaDummy136 f)),
        ((nb095AlphaDummy133 D R S_cls E), (nb095AlphaDummy135 f)),
        ((nb095AlphaDummy163 D R S_cls E), (nb095AlphaDummy164 f)),
        ((nb095AlphaDummy137 D R S_cls E), (nb095AlphaDummy138 f)),
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
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn, fv_syn_c0c]))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy091 D R S_cls E) ≠ (nb095AlphaDummy134 D R S_cls E) from (by
          unfold nb095AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy136 f) from (by
          unfold nb095AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy091 D R S_cls E) ≠ (nb095AlphaDummy133 D R S_cls E) from (by
          unfold nb095AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy135 f) from (by
          unfold nb095AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy163 D R S_cls E) from (by
          unfold nb095AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0154 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy164 f) from (by
          unfold nb095AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0155 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy137 D R S_cls E) from (by
          unfold nb095AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0151 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy138 f) from (by
          unfold nb095AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0153 f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy000 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy092 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy091 D R S_cls
        E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy094 f))).fv ∪
        ((Class.cv (nb095AlphaDummy093 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0048 x u D R S_cls f E))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy165 D R S_cls E), (nb095AlphaDummy166 f)),
        ((nb095AlphaDummy134 D R S_cls E), (nb095AlphaDummy136 f)),
        ((nb095AlphaDummy133 D R S_cls E), (nb095AlphaDummy135 f)),
        ((nb095AlphaDummy163 D R S_cls E), (nb095AlphaDummy164 f)),
        ((nb095AlphaDummy137 D R S_cls E), (nb095AlphaDummy138 f)),
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
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                        (nb095AlphaDummy000 D R S_cls E) ≠
                          (nb095AlphaDummy092 D R S_cls E) from (by
                          unfold nb095AlphaDummy092;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0170 D R S_cls E)
                                  1)))) (show f ≠ (nb095AlphaDummy094 f) from (by
                          unfold nb095AlphaDummy094;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0171 f) 1))))
                      (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                            (nb095AlphaDummy091 D R S_cls E) from (by
                            unfold nb095AlphaDummy091;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0170 D R S_cls E)
                                    0)))) (show f ≠ (nb095AlphaDummy093 f) from (by
                            unfold nb095AlphaDummy093;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0171 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                              (nb095AlphaDummy095 D R S_cls E) from (by
                              unfold nb095AlphaDummy095;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0168 D R S_cls E)
                                      0)))) (show f ≠ (nb095AlphaDummy096 f) from (by
                              unfold nb095AlphaDummy096;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0169 f) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                (nb095AlphaDummy466 D R S_cls E) from (by
                                unfold nb095AlphaDummy466;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0560 D R S_cls E) 1))))
                            (show f ≠ (nb095AlphaDummy468 f) from (by
                                unfold nb095AlphaDummy468;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0561 f) 1))))
                            (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                  (nb095AlphaDummy465 D R S_cls E) from (by
                                  unfold nb095AlphaDummy465;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0560 D R S_cls E) 0))))
                              (show f ≠ (nb095AlphaDummy467 f) from (by
                                  unfold nb095AlphaDummy467;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0561 f) 0))))
                              (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                    (nb095AlphaDummy469 D R S_cls E) from (by
                                    unfold nb095AlphaDummy469;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0558 D R S_cls E) 0))))
                                (show f ≠ (nb095AlphaDummy470 f) from (by
                                    unfold nb095AlphaDummy470;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0559 f)
                                            0)))) (TAlphaVar.there (show
                                    (nb095AlphaDummy000 D R S_cls E) ≠
                                      (nb095AlphaDummy387 D R S_cls E) from (by
                                      unfold nb095AlphaDummy387;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0554 D R S_cls E) 2))))
                                  (show f ≠ (nb095AlphaDummy390 f) from (by
                                      unfold nb095AlphaDummy390;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0556 f)
                                              2)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy000 D R S_cls E) ≠
                                        (nb095AlphaDummy386 D R S_cls E) from (by
                                        unfold nb095AlphaDummy386;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0554 D R S_cls E) 1))))
                                    (show f ≠ (nb095AlphaDummy389 f) from (by
                                        unfold nb095AlphaDummy389;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0556 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy385 D R S_cls E) from (by
                                          unfold nb095AlphaDummy385;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0554 D R S_cls E)
                                                  0)))) (show f ≠ (nb095AlphaDummy388 f) from
                                        (by
                                          unfold nb095AlphaDummy388;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0556 f) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy391 D R S_cls E) from (by
          unfold nb095AlphaDummy391;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0555 D R S_cls E)
                  0)))) (show f ≠ (nb095AlphaDummy392 f) from (by
          unfold nb095AlphaDummy392;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0557 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy383 D R S_cls E) from (by
          unfold nb095AlphaDummy383;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0552 D R S_cls E)
                  0)))) (show f ≠ (nb095AlphaDummy384 f) from (by
          unfold nb095AlphaDummy384;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0553 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy381 D R S_cls E) from (by
          unfold nb095AlphaDummy381;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0550 D R S_cls
                    E)
                  0)))) (show f ≠ (nb095AlphaDummy382 f) from (by
          unfold nb095AlphaDummy382;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0551 f) 0)))) (TAlphaVar.there (freshVar_injective
        ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_u (TAlphaVar.there
        (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_x
        (TAlphaVar.here _ _ _))))))))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0050`. -/
@[expose]
noncomputable def nb095SplitAlpha0050 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy549 D R S_cls E), (nb095AlphaDummy550 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy549 D R S_cls E))
          (Class.cab (nb095AlphaDummy543 D R S_cls E)
            (synWrex (nb095AlphaDummy544 D R S_cls E)
              (Class.cv (nb095AlphaDummy387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy549 D R S_cls E))
            (Class.cab (nb095AlphaDummy543 D R S_cls E)
              (synWrex (nb095AlphaDummy544 D R S_cls E)
                (Class.cv (nb095AlphaDummy387 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy550 f))
          (Class.cab (nb095AlphaDummy545 f)
            (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy390 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                (synCphi (Class.cv (nb095AlphaDummy546 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy550 f))
            (Class.cab (nb095AlphaDummy545 f)
              (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy390 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                  (synCphi (Class.cv (nb095AlphaDummy546 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy387 D R S_cls E) ≠
                      (nb095AlphaDummy544 D R S_cls E) from (by
                      unfold nb095AlphaDummy544;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E) 1))))
                  (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy546 f) from (by
                      unfold nb095AlphaDummy546;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0564 f) 1))))
                  (TAlphaVar.there (show (nb095AlphaDummy387 D R S_cls E) ≠
                        (nb095AlphaDummy543 D R S_cls E) from (by
                        unfold nb095AlphaDummy543;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E) 0))))
                    (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy545 f) from (by
                        unfold nb095AlphaDummy545;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0564 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy387 D R S_cls E) ≠
                          (nb095AlphaDummy549 D R S_cls E) from (by
                          unfold nb095AlphaDummy549;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0566 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy550 f) from (by
                          unfold nb095AlphaDummy550;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0567 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy387 D R S_cls E) ≠
                            (nb095AlphaDummy547 D R S_cls E) from (by
                            unfold nb095AlphaDummy547;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0563 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy548 f) from (by
                            unfold nb095AlphaDummy548;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0565 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy390 f))).fv ∪
                      ((Class.cv (nb095AlphaDummy389 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy544 D R S_cls E) ≠
                              (nb095AlphaDummy551 D R S_cls E) from (by
                              unfold nb095AlphaDummy551;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0568 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy553 f) from (by
                              unfold nb095AlphaDummy553;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0569 f) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy544 D R S_cls E) ≠
                                (nb095AlphaDummy552 D R S_cls E) from (by
                                unfold nb095AlphaDummy552;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0568 D R S_cls E) 1))))
                            (show (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy554 f) from (by
                                unfold nb095AlphaDummy554;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0569 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy544 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy546 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy551 D R S_cls E) ≠
        (nb095AlphaDummy558 D R S_cls E) from (by
          unfold nb095AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy561 f) from (by
          unfold nb095AlphaDummy561;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy551 D R S_cls E) ≠ (nb095AlphaDummy557 D R S_cls E) from (by
          unfold nb095AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy560 f) from (by
          unfold nb095AlphaDummy560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy551 D R S_cls E) ≠ (nb095AlphaDummy555 D R S_cls E) from (by
          unfold nb095AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0570 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from (by
          unfold nb095AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0571 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy559 D R S_cls E), (nb095AlphaDummy562 f)),
        ((nb095AlphaDummy558 D R S_cls E), (nb095AlphaDummy561 f)),
        ((nb095AlphaDummy557 D R S_cls E), (nb095AlphaDummy560 f)),
        ((nb095AlphaDummy555 D R S_cls E), (nb095AlphaDummy556 f)),
        ((nb095AlphaDummy551 D R S_cls E), (nb095AlphaDummy553 f)),
        ((nb095AlphaDummy552 D R S_cls E), (nb095AlphaDummy554 f)),
        ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
        ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
        ((nb095AlphaDummy549 D R S_cls E), (nb095AlphaDummy550 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy558
        D R S_cls E) ≠ (nb095AlphaDummy565 D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy559 D R S_cls E), (nb095AlphaDummy562 f)),
        ((nb095AlphaDummy558 D R S_cls E), (nb095AlphaDummy561 f)),
        ((nb095AlphaDummy557 D R S_cls E), (nb095AlphaDummy560 f)),
        ((nb095AlphaDummy555 D R S_cls E), (nb095AlphaDummy556 f)),
        ((nb095AlphaDummy551 D R S_cls E), (nb095AlphaDummy553 f)),
        ((nb095AlphaDummy552 D R S_cls E), (nb095AlphaDummy554 f)),
        ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
        ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
        ((nb095AlphaDummy549 D R S_cls E), (nb095AlphaDummy550 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy569
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy570 f) from (by
          unfold
            nb095AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy569
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy570 f) from (by
          unfold
            nb095AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy559
        D R S_cls E) ≠ (nb095AlphaDummy571 D R S_cls E) from (by
          unfold
            nb095AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy572 f) from (by
          unfold
            nb095AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy559
        D R S_cls E) ≠ (nb095AlphaDummy571 D R S_cls E) from (by
          unfold
            nb095AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy572 f) from (by
          unfold
            nb095AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy551 D R S_cls E) ≠
                                        (nb095AlphaDummy555 D R S_cls E) from (by
                                        unfold nb095AlphaDummy555;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from
                                      (by
                                        unfold nb095AlphaDummy556;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0571 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy555 D R S_cls E),
                                      (nb095AlphaDummy556 f)),
                                    ((nb095AlphaDummy551 D R S_cls E),
                                      (nb095AlphaDummy553 f)),
                                    ((nb095AlphaDummy552 D R S_cls E),
                                      (nb095AlphaDummy554 f)),
                                    ((nb095AlphaDummy544 D R S_cls E),
                                      (nb095AlphaDummy546 f)),
                                    ((nb095AlphaDummy543 D R S_cls E),
                                      (nb095AlphaDummy545 f)),
                                    ((nb095AlphaDummy549 D R S_cls E),
                                      (nb095AlphaDummy550 f)),
                                    ((nb095AlphaDummy547 D R S_cls E),
                                      (nb095AlphaDummy548 f)),
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
                                    (nb095AlphaDummy551 D R S_cls E) ≠
                                      (nb095AlphaDummy555 D R S_cls E) from (by
                                      unfold nb095AlphaDummy555;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from
                                    (by
                                      unfold nb095AlphaDummy556;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0571 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy551 D R S_cls E) ≠
                                        (nb095AlphaDummy555 D R S_cls E) from (by
                                        unfold nb095AlphaDummy555;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from
                                      (by
                                        unfold nb095AlphaDummy556;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0571 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy555 D R S_cls E),
                                      (nb095AlphaDummy556 f)),
                                    ((nb095AlphaDummy551 D R S_cls E),
                                      (nb095AlphaDummy553 f)),
                                    ((nb095AlphaDummy552 D R S_cls E),
                                      (nb095AlphaDummy554 f)),
                                    ((nb095AlphaDummy544 D R S_cls E),
                                      (nb095AlphaDummy546 f)),
                                    ((nb095AlphaDummy543 D R S_cls E),
                                      (nb095AlphaDummy545 f)),
                                    ((nb095AlphaDummy549 D R S_cls E),
                                      (nb095AlphaDummy550 f)),
                                    ((nb095AlphaDummy547 D R S_cls E),
                                      (nb095AlphaDummy548 f)),
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
                  (TAlphaVar.there (show (nb095AlphaDummy387 D R S_cls E) ≠
                        (nb095AlphaDummy544 D R S_cls E) from (by
                        unfold nb095AlphaDummy544;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E) 1))))
                    (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy546 f) from (by
                        unfold nb095AlphaDummy546;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0564 f) 1)))) (TAlphaVar.there
                      (show (nb095AlphaDummy387 D R S_cls E) ≠
                          (nb095AlphaDummy543 D R S_cls E) from (by
                          unfold nb095AlphaDummy543;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy545 f) from (by
                          unfold nb095AlphaDummy545;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0564 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy387 D R S_cls E) ≠
                            (nb095AlphaDummy549 D R S_cls E) from (by
                            unfold nb095AlphaDummy549;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0566 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy550 f) from (by
                            unfold nb095AlphaDummy550;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0567 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy387 D R S_cls E) ≠
                              (nb095AlphaDummy547 D R S_cls E) from (by
                              unfold nb095AlphaDummy547;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0563 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy548 f) from (by
                              unfold nb095AlphaDummy548;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0565 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy390 f))).fv ∪
                        ((Class.cv (nb095AlphaDummy389 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy544 D R S_cls E) ≠
                                (nb095AlphaDummy551 D R S_cls E) from (by
                                unfold nb095AlphaDummy551;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0568 D R S_cls E) 0))))
                            (show (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy553 f) from (by
                                unfold nb095AlphaDummy553;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0569 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy544 D R S_cls E) ≠
                                  (nb095AlphaDummy552 D R S_cls E) from (by
                                  unfold nb095AlphaDummy552;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0568 D R S_cls E) 1))))
                              (show (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy554 f) from
                                (by
                                  unfold nb095AlphaDummy554;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0569 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy544 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy546 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy551 D R S_cls E) ≠ (nb095AlphaDummy558 D R S_cls E) from (by
          unfold nb095AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy561 f) from (by
          unfold nb095AlphaDummy561;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy551 D R S_cls E) ≠ (nb095AlphaDummy557 D R S_cls E) from (by
          unfold nb095AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy560 f) from (by
          unfold nb095AlphaDummy560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy551 D R S_cls E) ≠
        (nb095AlphaDummy555 D R S_cls E) from (by
          unfold nb095AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0570 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from (by
          unfold nb095AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0571 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy559 D R S_cls E), (nb095AlphaDummy562 f)),
        ((nb095AlphaDummy558 D R S_cls E), (nb095AlphaDummy561 f)),
        ((nb095AlphaDummy557 D R S_cls E), (nb095AlphaDummy560 f)),
        ((nb095AlphaDummy555 D R S_cls E), (nb095AlphaDummy556 f)),
        ((nb095AlphaDummy551 D R S_cls E), (nb095AlphaDummy553 f)),
        ((nb095AlphaDummy552 D R S_cls E), (nb095AlphaDummy554 f)),
        ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
        ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
        ((nb095AlphaDummy549 D R S_cls E), (nb095AlphaDummy550 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy558
        D R S_cls E) ≠ (nb095AlphaDummy565 D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy559 D R S_cls E), (nb095AlphaDummy562 f)),
        ((nb095AlphaDummy558 D R S_cls E), (nb095AlphaDummy561 f)),
        ((nb095AlphaDummy557 D R S_cls E), (nb095AlphaDummy560 f)),
        ((nb095AlphaDummy555 D R S_cls E), (nb095AlphaDummy556 f)),
        ((nb095AlphaDummy551 D R S_cls E), (nb095AlphaDummy553 f)),
        ((nb095AlphaDummy552 D R S_cls E), (nb095AlphaDummy554 f)),
        ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
        ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
        ((nb095AlphaDummy549 D R S_cls E), (nb095AlphaDummy550 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy569
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy570 f) from (by
          unfold
            nb095AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy569
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy570 f) from (by
          unfold
            nb095AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy559
        D R S_cls E) ≠ (nb095AlphaDummy571 D R S_cls E) from (by
          unfold
            nb095AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy572 f) from (by
          unfold
            nb095AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy559
        D R S_cls E) ≠ (nb095AlphaDummy571 D R S_cls E) from (by
          unfold
            nb095AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy572 f) from (by
          unfold
            nb095AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy551 D R S_cls E) ≠
        (nb095AlphaDummy555 D R S_cls E) from (by
                                          unfold nb095AlphaDummy555;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0570 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy553 f) ≠
        (nb095AlphaDummy556 f) from (by
                                          unfold nb095AlphaDummy556;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0571 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy555 D R S_cls E),
                                        (nb095AlphaDummy556 f)),
                                      ((nb095AlphaDummy551 D R S_cls E),
                                        (nb095AlphaDummy553 f)),
                                      ((nb095AlphaDummy552 D R S_cls E),
                                        (nb095AlphaDummy554 f)),
                                      ((nb095AlphaDummy544 D R S_cls E),
                                        (nb095AlphaDummy546 f)),
                                      ((nb095AlphaDummy543 D R S_cls E),
                                        (nb095AlphaDummy545 f)),
                                      ((nb095AlphaDummy549 D R S_cls E),
                                        (nb095AlphaDummy550 f)),
                                      ((nb095AlphaDummy547 D R S_cls E),
                                        (nb095AlphaDummy548 f)),
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
                                      (nb095AlphaDummy551 D R S_cls E) ≠
                                        (nb095AlphaDummy555 D R S_cls E) from (by
                                        unfold nb095AlphaDummy555;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from
                                      (by
                                        unfold nb095AlphaDummy556;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0571 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy551 D R S_cls E) ≠
        (nb095AlphaDummy555 D R S_cls E) from (by
                                          unfold nb095AlphaDummy555;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0570 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy553 f) ≠
        (nb095AlphaDummy556 f) from (by
                                          unfold nb095AlphaDummy556;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0571 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy555 D R S_cls E),
                                        (nb095AlphaDummy556 f)),
                                      ((nb095AlphaDummy551 D R S_cls E),
                                        (nb095AlphaDummy553 f)),
                                      ((nb095AlphaDummy552 D R S_cls E),
                                        (nb095AlphaDummy554 f)),
                                      ((nb095AlphaDummy544 D R S_cls E),
                                        (nb095AlphaDummy546 f)),
                                      ((nb095AlphaDummy543 D R S_cls E),
                                        (nb095AlphaDummy545 f)),
                                      ((nb095AlphaDummy549 D R S_cls E),
                                        (nb095AlphaDummy550 f)),
                                      ((nb095AlphaDummy547 D R S_cls E),
                                        (nb095AlphaDummy548 f)),
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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0051`. -/
@[expose]
noncomputable def nb095SplitAlpha0051 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy575 D R S_cls E), (nb095AlphaDummy576 f)),
        ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
        ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
        ((nb095AlphaDummy573 D R S_cls E), (nb095AlphaDummy574 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.classMem (Class.cv (nb095AlphaDummy575 D R S_cls E))
        (synCcompl (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))))
      (Wff.classMem (Class.cv (nb095AlphaDummy576 f))
        (synCcompl (synCphi (Class.cv (nb095AlphaDummy546 f))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095AlphaDummy544 D R S_cls E) ≠
                            (nb095AlphaDummy551 D R S_cls E) from (by
                            unfold nb095AlphaDummy551;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0568 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy553 f) from (by
                            unfold nb095AlphaDummy553;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0569 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy544 D R S_cls E) ≠
                              (nb095AlphaDummy552 D R S_cls E) from (by
                              unfold nb095AlphaDummy552;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0568 D R S_cls E)
                                      1))))
                          (show (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy554 f) from (by
                              unfold nb095AlphaDummy554;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0569 f) 1))))
                          (TAlphaVar.there (show (nb095AlphaDummy544 D R S_cls E) ≠
                                (nb095AlphaDummy577 D R S_cls E) from (by
                                unfold nb095AlphaDummy577;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0598 D R S_cls E) 0))))
                            (show (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy578 f) from (by
                                unfold nb095AlphaDummy578;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0599 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy544 D R S_cls E) ≠
                                  (nb095AlphaDummy575 D R S_cls E) from (by
                                  unfold nb095AlphaDummy575;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0596 D R S_cls E) 0))))
                              (show (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy576 f) from
                                (by
                                  unfold nb095AlphaDummy576;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0597 f) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb095AlphaDummy544 D R S_cls E))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb095AlphaDummy546 f))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095AlphaDummy551 D R S_cls E) ≠ (nb095AlphaDummy558 D R S_cls E) from (by
          unfold nb095AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R S_cls E)
                  1)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy561 f) from (by
          unfold nb095AlphaDummy561;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy551 D R S_cls E) ≠ (nb095AlphaDummy557 D R S_cls E) from (by
          unfold nb095AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy560 f) from (by
          unfold nb095AlphaDummy560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy551 D R S_cls E) ≠ (nb095AlphaDummy555 D R S_cls E) from (by
          unfold nb095AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0570 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from (by
          unfold nb095AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0571 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy559 D R S_cls E), (nb095AlphaDummy562 f)),
        ((nb095AlphaDummy558 D R S_cls E), (nb095AlphaDummy561 f)),
        ((nb095AlphaDummy557 D R S_cls E), (nb095AlphaDummy560 f)),
        ((nb095AlphaDummy555 D R S_cls E), (nb095AlphaDummy556 f)),
        ((nb095AlphaDummy551 D R S_cls E), (nb095AlphaDummy553 f)),
        ((nb095AlphaDummy552 D R S_cls E), (nb095AlphaDummy554 f)),
        ((nb095AlphaDummy577 D R S_cls E), (nb095AlphaDummy578 f)),
        ((nb095AlphaDummy575 D R S_cls E), (nb095AlphaDummy576 f)),
        ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
        ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
        ((nb095AlphaDummy573 D R S_cls E), (nb095AlphaDummy574 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
                                        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy559 D R S_cls E), (nb095AlphaDummy562 f)),
        ((nb095AlphaDummy558 D R S_cls E), (nb095AlphaDummy561 f)),
        ((nb095AlphaDummy557 D R S_cls E), (nb095AlphaDummy560 f)),
        ((nb095AlphaDummy555 D R S_cls E), (nb095AlphaDummy556 f)),
        ((nb095AlphaDummy551 D R S_cls E), (nb095AlphaDummy553 f)),
        ((nb095AlphaDummy552 D R S_cls E), (nb095AlphaDummy554 f)),
        ((nb095AlphaDummy577 D R S_cls E), (nb095AlphaDummy578 f)),
        ((nb095AlphaDummy575 D R S_cls E), (nb095AlphaDummy576 f)),
        ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
        ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
        ((nb095AlphaDummy573 D R S_cls E), (nb095AlphaDummy574 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy558 D
        R S_cls E) ≠ (nb095AlphaDummy569 D R S_cls E) from (by
          unfold
            nb095AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy570 f) from (by
          unfold
            nb095AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy569
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy570 f) from (by
          unfold
            nb095AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy559 D
        R S_cls E) ≠ (nb095AlphaDummy571 D R S_cls E) from (by
          unfold
            nb095AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy572 f) from (by
          unfold
            nb095AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy559 D
        R S_cls E) ≠ (nb095AlphaDummy571 D R S_cls E) from (by
          unfold
            nb095AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy572 f) from (by
          unfold
            nb095AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy551 D R S_cls E) ≠
                                      (nb095AlphaDummy555 D R S_cls E) from (by
                                      unfold nb095AlphaDummy555;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from
                                    (by
                                      unfold nb095AlphaDummy556;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0571 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed [((nb095AlphaDummy555 D R S_cls E),
                                    (nb095AlphaDummy556 f)),
                                  ((nb095AlphaDummy551 D R S_cls E),
                                    (nb095AlphaDummy553 f)),
                                  ((nb095AlphaDummy552 D R S_cls E),
                                    (nb095AlphaDummy554 f)),
                                  ((nb095AlphaDummy577 D R S_cls E),
                                    (nb095AlphaDummy578 f)),
                                  ((nb095AlphaDummy575 D R S_cls E),
                                    (nb095AlphaDummy576 f)),
                                  ((nb095AlphaDummy544 D R S_cls E),
                                    (nb095AlphaDummy546 f)),
                                  ((nb095AlphaDummy543 D R S_cls E),
                                    (nb095AlphaDummy545 f)),
                                  ((nb095AlphaDummy573 D R S_cls E),
                                    (nb095AlphaDummy574 f)),
                                  ((nb095AlphaDummy547 D R S_cls E),
                                    (nb095AlphaDummy548 f)),
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
                                  (nb095AlphaDummy551 D R S_cls E) ≠
                                    (nb095AlphaDummy555 D R S_cls E) from (by
                                    unfold nb095AlphaDummy555;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from (by
                                    unfold nb095AlphaDummy556;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0571 f)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy551 D R S_cls E) ≠
                                      (nb095AlphaDummy555 D R S_cls E) from (by
                                      unfold nb095AlphaDummy555;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from
                                    (by
                                      unfold nb095AlphaDummy556;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0571 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed [((nb095AlphaDummy555 D R S_cls E),
                                    (nb095AlphaDummy556 f)),
                                  ((nb095AlphaDummy551 D R S_cls E),
                                    (nb095AlphaDummy553 f)),
                                  ((nb095AlphaDummy552 D R S_cls E),
                                    (nb095AlphaDummy554 f)),
                                  ((nb095AlphaDummy577 D R S_cls E),
                                    (nb095AlphaDummy578 f)),
                                  ((nb095AlphaDummy575 D R S_cls E),
                                    (nb095AlphaDummy576 f)),
                                  ((nb095AlphaDummy544 D R S_cls E),
                                    (nb095AlphaDummy546 f)),
                                  ((nb095AlphaDummy543 D R S_cls E),
                                    (nb095AlphaDummy545 f)),
                                  ((nb095AlphaDummy573 D R S_cls E),
                                    (nb095AlphaDummy574 f)),
                                  ((nb095AlphaDummy547 D R S_cls E),
                                    (nb095AlphaDummy548 f)),
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
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095AlphaDummy544 D R S_cls E) ≠
                            (nb095AlphaDummy551 D R S_cls E) from (by
                            unfold nb095AlphaDummy551;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0568 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy553 f) from (by
                            unfold nb095AlphaDummy553;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0569 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy544 D R S_cls E) ≠
                              (nb095AlphaDummy552 D R S_cls E) from (by
                              unfold nb095AlphaDummy552;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0568 D R S_cls E)
                                      1))))
                          (show (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy554 f) from (by
                              unfold nb095AlphaDummy554;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0569 f) 1))))
                          (TAlphaVar.there (show (nb095AlphaDummy544 D R S_cls E) ≠
                                (nb095AlphaDummy577 D R S_cls E) from (by
                                unfold nb095AlphaDummy577;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0598 D R S_cls E) 0))))
                            (show (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy578 f) from (by
                                unfold nb095AlphaDummy578;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0599 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy544 D R S_cls E) ≠
                                  (nb095AlphaDummy575 D R S_cls E) from (by
                                  unfold nb095AlphaDummy575;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0596 D R S_cls E) 0))))
                              (show (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy576 f) from
                                (by
                                  unfold nb095AlphaDummy576;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0597 f) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb095AlphaDummy544 D R S_cls E))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb095AlphaDummy546 f))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095AlphaDummy551 D R S_cls E) ≠ (nb095AlphaDummy558 D R S_cls E) from (by
          unfold nb095AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R S_cls E)
                  1)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy561 f) from (by
          unfold nb095AlphaDummy561;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy551 D R S_cls E) ≠ (nb095AlphaDummy557 D R S_cls E) from (by
          unfold nb095AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy560 f) from (by
          unfold nb095AlphaDummy560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy551 D R S_cls E) ≠ (nb095AlphaDummy555 D R S_cls E) from (by
          unfold nb095AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0570 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from (by
          unfold nb095AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0571 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy559 D R S_cls E), (nb095AlphaDummy562 f)),
        ((nb095AlphaDummy558 D R S_cls E), (nb095AlphaDummy561 f)),
        ((nb095AlphaDummy557 D R S_cls E), (nb095AlphaDummy560 f)),
        ((nb095AlphaDummy555 D R S_cls E), (nb095AlphaDummy556 f)),
        ((nb095AlphaDummy551 D R S_cls E), (nb095AlphaDummy553 f)),
        ((nb095AlphaDummy552 D R S_cls E), (nb095AlphaDummy554 f)),
        ((nb095AlphaDummy577 D R S_cls E), (nb095AlphaDummy578 f)),
        ((nb095AlphaDummy575 D R S_cls E), (nb095AlphaDummy576 f)),
        ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
        ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
        ((nb095AlphaDummy573 D R S_cls E), (nb095AlphaDummy574 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
                                        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy559 D R S_cls E), (nb095AlphaDummy562 f)),
        ((nb095AlphaDummy558 D R S_cls E), (nb095AlphaDummy561 f)),
        ((nb095AlphaDummy557 D R S_cls E), (nb095AlphaDummy560 f)),
        ((nb095AlphaDummy555 D R S_cls E), (nb095AlphaDummy556 f)),
        ((nb095AlphaDummy551 D R S_cls E), (nb095AlphaDummy553 f)),
        ((nb095AlphaDummy552 D R S_cls E), (nb095AlphaDummy554 f)),
        ((nb095AlphaDummy577 D R S_cls E), (nb095AlphaDummy578 f)),
        ((nb095AlphaDummy575 D R S_cls E), (nb095AlphaDummy576 f)),
        ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
        ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
        ((nb095AlphaDummy573 D R S_cls E), (nb095AlphaDummy574 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy558 D
        R S_cls E) ≠ (nb095AlphaDummy569 D R S_cls E) from (by
          unfold
            nb095AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy570 f) from (by
          unfold
            nb095AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy569
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy570 f) from (by
          unfold
            nb095AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy559 D
        R S_cls E) ≠ (nb095AlphaDummy571 D R S_cls E) from (by
          unfold
            nb095AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy572 f) from (by
          unfold
            nb095AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy559 D
        R S_cls E) ≠ (nb095AlphaDummy571 D R S_cls E) from (by
          unfold
            nb095AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy572 f) from (by
          unfold
            nb095AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy551 D R S_cls E) ≠
                                      (nb095AlphaDummy555 D R S_cls E) from (by
                                      unfold nb095AlphaDummy555;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from
                                    (by
                                      unfold nb095AlphaDummy556;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0571 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed [((nb095AlphaDummy555 D R S_cls E),
                                    (nb095AlphaDummy556 f)),
                                  ((nb095AlphaDummy551 D R S_cls E),
                                    (nb095AlphaDummy553 f)),
                                  ((nb095AlphaDummy552 D R S_cls E),
                                    (nb095AlphaDummy554 f)),
                                  ((nb095AlphaDummy577 D R S_cls E),
                                    (nb095AlphaDummy578 f)),
                                  ((nb095AlphaDummy575 D R S_cls E),
                                    (nb095AlphaDummy576 f)),
                                  ((nb095AlphaDummy544 D R S_cls E),
                                    (nb095AlphaDummy546 f)),
                                  ((nb095AlphaDummy543 D R S_cls E),
                                    (nb095AlphaDummy545 f)),
                                  ((nb095AlphaDummy573 D R S_cls E),
                                    (nb095AlphaDummy574 f)),
                                  ((nb095AlphaDummy547 D R S_cls E),
                                    (nb095AlphaDummy548 f)),
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
                                  (nb095AlphaDummy551 D R S_cls E) ≠
                                    (nb095AlphaDummy555 D R S_cls E) from (by
                                    unfold nb095AlphaDummy555;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from (by
                                    unfold nb095AlphaDummy556;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0571 f)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy551 D R S_cls E) ≠
                                      (nb095AlphaDummy555 D R S_cls E) from (by
                                      unfold nb095AlphaDummy555;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from
                                    (by
                                      unfold nb095AlphaDummy556;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0571 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed [((nb095AlphaDummy555 D R S_cls E),
                                    (nb095AlphaDummy556 f)),
                                  ((nb095AlphaDummy551 D R S_cls E),
                                    (nb095AlphaDummy553 f)),
                                  ((nb095AlphaDummy552 D R S_cls E),
                                    (nb095AlphaDummy554 f)),
                                  ((nb095AlphaDummy577 D R S_cls E),
                                    (nb095AlphaDummy578 f)),
                                  ((nb095AlphaDummy575 D R S_cls E),
                                    (nb095AlphaDummy576 f)),
                                  ((nb095AlphaDummy544 D R S_cls E),
                                    (nb095AlphaDummy546 f)),
                                  ((nb095AlphaDummy543 D R S_cls E),
                                    (nb095AlphaDummy545 f)),
                                  ((nb095AlphaDummy573 D R S_cls E),
                                    (nb095AlphaDummy574 f)),
                                  ((nb095AlphaDummy547 D R S_cls E),
                                    (nb095AlphaDummy548 f)),
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


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
