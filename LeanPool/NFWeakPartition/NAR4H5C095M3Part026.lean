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

@[expose]
noncomputable def nb095_split_alpha_0049 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_f_u : f ≠ u) (dv_f_x : f ≠ x) :
    TAlphaWff
      [((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
        ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
        ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_383 D R S_cls E), (nb095_alpha_dummy_384 f)),
        ((nb095_alpha_dummy_381 D R S_cls E), (nb095_alpha_dummy_382 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classEq (Class.cv (nb095_alpha_dummy_469 D R S_cls E))
          (syn_cop (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_466 D R S_cls E)))) (Wff.neg
          (syn_wbr (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
            (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
            (Class.cv (nb095_alpha_dummy_465 D R S_cls E)))))
      (Wff.imp (Wff.classEq (Class.cv (nb095_alpha_dummy_470 f))
          (syn_cop (Class.cv (nb095_alpha_dummy_467 f)) (Class.cv (nb095_alpha_dummy_468 f))))
        (Wff.neg (syn_wbr (Class.cv (nb095_alpha_dummy_468 f)) (syn_ccnv (Class.cv f))
            (Class.cv (nb095_alpha_dummy_467 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
              (nb095_alpha_dummy_466 D R S_cls E) ≠ (nb095_alpha_dummy_469 D R S_cls E) from (by
                unfold nb095_alpha_dummy_469;
                with_reducible
                  exact
                    (Nat.ne_of_lt
                      (mem_lt_freshVar (nb095_support_mem_0472 D R S_cls E) 0))))) (Ne.symm
            (show (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_470 f) from (by
                unfold nb095_alpha_dummy_470;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0473 f) 0)))))
          (TAlphaVar.there (Ne.symm (show
                (nb095_alpha_dummy_465 D R S_cls E) ≠ (nb095_alpha_dummy_469 D R S_cls E) from
                (by
                  unfold nb095_alpha_dummy_469;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb095_support_mem_0470 D R S_cls E) 0))))) (Ne.symm
              (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_470 f) from (by
                  unfold nb095_alpha_dummy_470;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0471 f) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0041 x u D R S_cls f E)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_466 D R S_cls E) ≠
                                      (nb095_alpha_dummy_472 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_472;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0502 D R S_cls E) 1)))) (show
                                    (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_474 f) from
                                    (by
                                      unfold nb095_alpha_dummy_474;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0504 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb095_alpha_dummy_466 D R S_cls E) ≠
                                        (nb095_alpha_dummy_471 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_471;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0502 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_473 f) from
                                      (by
                                        unfold nb095_alpha_dummy_473;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0504 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_466 D R S_cls E) ≠
        (nb095_alpha_dummy_501 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_501;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0506 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_468 f) ≠
        (nb095_alpha_dummy_502 f) from (by
                                          unfold nb095_alpha_dummy_502;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0507 f) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_466 D R S_cls E) ≠ (nb095_alpha_dummy_475 D R S_cls E) from (by
          unfold nb095_alpha_dummy_475;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0503 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_476 f) from (by
          unfold nb095_alpha_dummy_476;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0505 f) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv ∪
                                      ((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv (nb095_alpha_dummy_467 f))).fv ∪
                                      ((Class.cv (nb095_alpha_dummy_468 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0042 x u D R S_cls f E))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((nb095_alpha_dummy_503 D R S_cls E),
        (nb095_alpha_dummy_504 f)), ((nb095_alpha_dummy_472 D R S_cls E),
        (nb095_alpha_dummy_474 f)), ((nb095_alpha_dummy_471 D R S_cls E),
        (nb095_alpha_dummy_473 f)), ((nb095_alpha_dummy_501 D R S_cls E),
        (nb095_alpha_dummy_502 f)), ((nb095_alpha_dummy_475 D R S_cls E),
        (nb095_alpha_dummy_476 f)), ((nb095_alpha_dummy_466 D R S_cls E),
        (nb095_alpha_dummy_468 f)), ((nb095_alpha_dummy_465 D R S_cls E),
        (nb095_alpha_dummy_467 f)), ((nb095_alpha_dummy_469 D R S_cls E),
        (nb095_alpha_dummy_470 f)), ((nb095_alpha_dummy_387 D R S_cls E),
        (nb095_alpha_dummy_390 f)), ((nb095_alpha_dummy_386 D R S_cls E),
        (nb095_alpha_dummy_389 f)), ((nb095_alpha_dummy_385 D R S_cls E),
        (nb095_alpha_dummy_388 f)), ((nb095_alpha_dummy_391 D R S_cls E),
        (nb095_alpha_dummy_392 f)), ((nb095_alpha_dummy_383 D R S_cls E),
        (nb095_alpha_dummy_384 f)), ((nb095_alpha_dummy_381 D R S_cls E),
        (nb095_alpha_dummy_382 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                        (syn_ccompl (syn_csn (syn_c0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c])))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_466 D R S_cls E) ≠
                                      (nb095_alpha_dummy_472 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_472;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0502 D R S_cls E) 1)))) (show
                                    (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_474 f) from
                                    (by
                                      unfold nb095_alpha_dummy_474;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0504 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb095_alpha_dummy_466 D R S_cls E) ≠
                                        (nb095_alpha_dummy_471 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_471;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0502 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_473 f) from
                                      (by
                                        unfold nb095_alpha_dummy_473;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0504 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_466 D R S_cls E) ≠
        (nb095_alpha_dummy_501 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_501;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0506 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_468 f) ≠
        (nb095_alpha_dummy_502 f) from (by
                                          unfold nb095_alpha_dummy_502;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0507 f) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_466 D R S_cls E) ≠ (nb095_alpha_dummy_475 D R S_cls E) from (by
          unfold nb095_alpha_dummy_475;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0503 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_476 f) from (by
          unfold nb095_alpha_dummy_476;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0505 f) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv ∪
                                      ((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv (nb095_alpha_dummy_467 f))).fv ∪
                                      ((Class.cv (nb095_alpha_dummy_468 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0042 x u D R S_cls f E))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((nb095_alpha_dummy_503 D R S_cls E),
        (nb095_alpha_dummy_504 f)), ((nb095_alpha_dummy_472 D R S_cls E),
        (nb095_alpha_dummy_474 f)), ((nb095_alpha_dummy_471 D R S_cls E),
        (nb095_alpha_dummy_473 f)), ((nb095_alpha_dummy_501 D R S_cls E),
        (nb095_alpha_dummy_502 f)), ((nb095_alpha_dummy_475 D R S_cls E),
        (nb095_alpha_dummy_476 f)), ((nb095_alpha_dummy_466 D R S_cls E),
        (nb095_alpha_dummy_468 f)), ((nb095_alpha_dummy_465 D R S_cls E),
        (nb095_alpha_dummy_467 f)), ((nb095_alpha_dummy_469 D R S_cls E),
        (nb095_alpha_dummy_470 f)), ((nb095_alpha_dummy_387 D R S_cls E),
        (nb095_alpha_dummy_390 f)), ((nb095_alpha_dummy_386 D R S_cls E),
        (nb095_alpha_dummy_389 f)), ((nb095_alpha_dummy_385 D R S_cls E),
        (nb095_alpha_dummy_388 f)), ((nb095_alpha_dummy_391 D R S_cls E),
        (nb095_alpha_dummy_392 f)), ((nb095_alpha_dummy_383 D R S_cls E),
        (nb095_alpha_dummy_384 f)), ((nb095_alpha_dummy_381 D R S_cls E),
        (nb095_alpha_dummy_382 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                        (syn_ccompl (syn_csn (syn_c0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0043 x u D R S_cls f E)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_465 D R S_cls E) ≠
                                        (nb095_alpha_dummy_508 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_508;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0540 D R S_cls E) 1)))) (show
                                      (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_510 f) from
                                      (by
                                        unfold nb095_alpha_dummy_510;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0542 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_465 D R S_cls E) ≠
        (nb095_alpha_dummy_507 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_507;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0540 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_467 f) ≠
        (nb095_alpha_dummy_509 f) from (by
                                          unfold nb095_alpha_dummy_509;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0542 f) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_465 D R S_cls E) ≠ (nb095_alpha_dummy_537 D R S_cls E) from (by
          unfold nb095_alpha_dummy_537;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0544 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_538 f) from (by
          unfold nb095_alpha_dummy_538;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0545 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_465 D R S_cls E) ≠ (nb095_alpha_dummy_511 D R S_cls E) from (by
          unfold nb095_alpha_dummy_511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0541 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_512 f) from (by
          unfold nb095_alpha_dummy_512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0543 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv) (by decide))
        (freshVar_injective (((syn_ccnv (Class.cv f))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_466 D R S_cls E))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_465 D R S_cls E))).fv) (by decide)) (freshVar_injective
                                      (((Class.cv (nb095_alpha_dummy_468 f))).fv ∪
                                        ((Class.cv (nb095_alpha_dummy_467 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0044 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_539 D R S_cls E), (nb095_alpha_dummy_540 f)),
        ((nb095_alpha_dummy_508 D R S_cls E), (nb095_alpha_dummy_510 f)),
        ((nb095_alpha_dummy_507 D R S_cls E), (nb095_alpha_dummy_509 f)),
        ((nb095_alpha_dummy_537 D R S_cls E), (nb095_alpha_dummy_538 f)),
        ((nb095_alpha_dummy_511 D R S_cls E), (nb095_alpha_dummy_512 f)),
        ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
        ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
        ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_383 D R S_cls E), (nb095_alpha_dummy_384 f)),
        ((nb095_alpha_dummy_381 D R S_cls E), (nb095_alpha_dummy_382 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_465 D R S_cls E) ≠
                                        (nb095_alpha_dummy_508 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_508;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0540 D R S_cls E) 1)))) (show
                                      (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_510 f) from
                                      (by
                                        unfold nb095_alpha_dummy_510;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0542 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_465 D R S_cls E) ≠
        (nb095_alpha_dummy_507 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_507;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0540 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_467 f) ≠
        (nb095_alpha_dummy_509 f) from (by
                                          unfold nb095_alpha_dummy_509;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0542 f) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_465 D R S_cls E) ≠ (nb095_alpha_dummy_537 D R S_cls E) from (by
          unfold nb095_alpha_dummy_537;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0544 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_538 f) from (by
          unfold nb095_alpha_dummy_538;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0545 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_465 D R S_cls E) ≠ (nb095_alpha_dummy_511 D R S_cls E) from (by
          unfold nb095_alpha_dummy_511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0541 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_512 f) from (by
          unfold nb095_alpha_dummy_512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0543 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv) (by decide))
        (freshVar_injective (((syn_ccnv (Class.cv f))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_466 D R S_cls E))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_465 D R S_cls E))).fv) (by decide)) (freshVar_injective
                                      (((Class.cv (nb095_alpha_dummy_468 f))).fv ∪
                                        ((Class.cv (nb095_alpha_dummy_467 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0044 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_539 D R S_cls E), (nb095_alpha_dummy_540 f)),
        ((nb095_alpha_dummy_508 D R S_cls E), (nb095_alpha_dummy_510 f)),
        ((nb095_alpha_dummy_507 D R S_cls E), (nb095_alpha_dummy_509 f)),
        ((nb095_alpha_dummy_537 D R S_cls E), (nb095_alpha_dummy_538 f)),
        ((nb095_alpha_dummy_511 D R S_cls E), (nb095_alpha_dummy_512 f)),
        ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
        ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
        ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_383 D R S_cls E), (nb095_alpha_dummy_384 f)),
        ((nb095_alpha_dummy_381 D R S_cls E), (nb095_alpha_dummy_382 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
              (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                          (nb095_alpha_dummy_092 D R S_cls E) ≠
                            (nb095_alpha_dummy_095 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_095;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0082 D R S_cls E)
                                    0))))) (Ne.symm
                        (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_096 f) from (by
                            unfold nb095_alpha_dummy_096;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0083 f) 0)))))
                      (TAlphaVar.there (Ne.symm (show (nb095_alpha_dummy_091 D R S_cls E) ≠
                              (nb095_alpha_dummy_095 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_095;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0080 D R S_cls E)
                                      0))))) (Ne.symm
                          (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_096 f) from (by
                              unfold nb095_alpha_dummy_096;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0081 f) 0)))))
                        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                (nb095_split_alpha_0045 x u D R S_cls f E)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_092 D R S_cls E) ≠ (nb095_alpha_dummy_098 D R S_cls E) from (by
          unfold nb095_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_100 f) from (by
          unfold nb095_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_092 D R S_cls E) ≠ (nb095_alpha_dummy_097 D R S_cls E) from (by
          unfold nb095_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_099 f) from (by
          unfold nb095_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_127 D R S_cls E) from (by
          unfold nb095_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0116 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_128 f) from (by
          unfold nb095_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0117 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_101 D R S_cls E) from (by
          unfold nb095_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0113 D
                    R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_102 f) from (by
          unfold nb095_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0115 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_091 D R S_cls
        E))).fv ∪ ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0046 x u D R S_cls f E))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_129 D R S_cls E), (nb095_alpha_dummy_130 f)),
        ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
        ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
        ((nb095_alpha_dummy_127 D R S_cls E), (nb095_alpha_dummy_128 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
        ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
        ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_383 D R S_cls E), (nb095_alpha_dummy_384 f)),
        ((nb095_alpha_dummy_381 D R S_cls E), (nb095_alpha_dummy_382 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn, fv_syn_c0c]))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_092 D R S_cls E) ≠ (nb095_alpha_dummy_098 D R S_cls E) from (by
          unfold nb095_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_100 f) from (by
          unfold nb095_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_092 D R S_cls E) ≠ (nb095_alpha_dummy_097 D R S_cls E) from (by
          unfold nb095_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_099 f) from (by
          unfold nb095_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_127 D R S_cls E) from (by
          unfold nb095_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0116 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_128 f) from (by
          unfold nb095_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0117 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_101 D R S_cls E) from (by
          unfold nb095_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0113 D
                    R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_102 f) from (by
          unfold nb095_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0115 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_091 D R S_cls
        E))).fv ∪ ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0046 x u D R S_cls f E))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_129 D R S_cls E), (nb095_alpha_dummy_130 f)),
        ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
        ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
        ((nb095_alpha_dummy_127 D R S_cls E), (nb095_alpha_dummy_128 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
        ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
        ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_383 D R S_cls E), (nb095_alpha_dummy_384 f)),
        ((nb095_alpha_dummy_381 D R S_cls E), (nb095_alpha_dummy_382 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                (nb095_split_alpha_0047 x u D R S_cls f E)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_091 D R S_cls E) ≠ (nb095_alpha_dummy_134 D R S_cls E) from (by
          unfold nb095_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_136 f) from (by
          unfold nb095_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_091 D R S_cls E) ≠ (nb095_alpha_dummy_133 D R S_cls E) from (by
          unfold nb095_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_135 f) from (by
          unfold nb095_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_163 D R S_cls E) from (by
          unfold nb095_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0154 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_164 f) from (by
          unfold nb095_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0155 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_137 D R S_cls E) from (by
          unfold nb095_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0151 D
                    R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_138 f) from (by
          unfold nb095_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0153 f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_000 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_092 D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_091 D R S_cls
        E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_094 f))).fv ∪
        ((Class.cv (nb095_alpha_dummy_093 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0048 x u D R S_cls f E))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_165 D R S_cls E), (nb095_alpha_dummy_166 f)),
        ((nb095_alpha_dummy_134 D R S_cls E), (nb095_alpha_dummy_136 f)),
        ((nb095_alpha_dummy_133 D R S_cls E), (nb095_alpha_dummy_135 f)),
        ((nb095_alpha_dummy_163 D R S_cls E), (nb095_alpha_dummy_164 f)),
        ((nb095_alpha_dummy_137 D R S_cls E), (nb095_alpha_dummy_138 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
        ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
        ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_383 D R S_cls E), (nb095_alpha_dummy_384 f)),
        ((nb095_alpha_dummy_381 D R S_cls E), (nb095_alpha_dummy_382 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn, fv_syn_c0c]))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_091 D R S_cls E) ≠ (nb095_alpha_dummy_134 D R S_cls E) from (by
          unfold nb095_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_136 f) from (by
          unfold nb095_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_091 D R S_cls E) ≠ (nb095_alpha_dummy_133 D R S_cls E) from (by
          unfold nb095_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_135 f) from (by
          unfold nb095_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_163 D R S_cls E) from (by
          unfold nb095_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0154 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_164 f) from (by
          unfold nb095_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0155 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_137 D R S_cls E) from (by
          unfold nb095_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0151 D
                    R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_138 f) from (by
          unfold nb095_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0153 f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_000 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_092 D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_091 D R S_cls
        E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_094 f))).fv ∪
        ((Class.cv (nb095_alpha_dummy_093 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0048 x u D R S_cls f E))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_165 D R S_cls E), (nb095_alpha_dummy_166 f)),
        ((nb095_alpha_dummy_134 D R S_cls E), (nb095_alpha_dummy_136 f)),
        ((nb095_alpha_dummy_133 D R S_cls E), (nb095_alpha_dummy_135 f)),
        ((nb095_alpha_dummy_163 D R S_cls E), (nb095_alpha_dummy_164 f)),
        ((nb095_alpha_dummy_137 D R S_cls E), (nb095_alpha_dummy_138 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
        ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
        ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_383 D R S_cls E), (nb095_alpha_dummy_384 f)),
        ((nb095_alpha_dummy_381 D R S_cls E), (nb095_alpha_dummy_382 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                        (nb095_alpha_dummy_000 D R S_cls E) ≠
                          (nb095_alpha_dummy_092 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_092;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0170 D R S_cls E)
                                  1)))) (show f ≠ (nb095_alpha_dummy_094 f) from (by
                          unfold nb095_alpha_dummy_094;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0171 f) 1))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                            (nb095_alpha_dummy_091 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_091;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0170 D R S_cls E)
                                    0)))) (show f ≠ (nb095_alpha_dummy_093 f) from (by
                            unfold nb095_alpha_dummy_093;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0171 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                              (nb095_alpha_dummy_095 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_095;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0168 D R S_cls E)
                                      0)))) (show f ≠ (nb095_alpha_dummy_096 f) from (by
                              unfold nb095_alpha_dummy_096;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0169 f) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                                (nb095_alpha_dummy_466 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_466;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0560 D R S_cls E) 1))))
                            (show f ≠ (nb095_alpha_dummy_468 f) from (by
                                unfold nb095_alpha_dummy_468;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0561 f) 1))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                                  (nb095_alpha_dummy_465 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_465;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0560 D R S_cls E) 0))))
                              (show f ≠ (nb095_alpha_dummy_467 f) from (by
                                  unfold nb095_alpha_dummy_467;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0561 f) 0))))
                              (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                                    (nb095_alpha_dummy_469 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_469;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0558 D R S_cls E) 0))))
                                (show f ≠ (nb095_alpha_dummy_470 f) from (by
                                    unfold nb095_alpha_dummy_470;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0559 f)
                                            0)))) (TAlphaVar.there (show
                                    (nb095_alpha_dummy_000 D R S_cls E) ≠
                                      (nb095_alpha_dummy_387 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_387;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0554 D R S_cls E) 2))))
                                  (show f ≠ (nb095_alpha_dummy_390 f) from (by
                                      unfold nb095_alpha_dummy_390;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0556 f)
                                              2)))) (TAlphaVar.there (show
                                      (nb095_alpha_dummy_000 D R S_cls E) ≠
                                        (nb095_alpha_dummy_386 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_386;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0554 D R S_cls E) 1))))
                                    (show f ≠ (nb095_alpha_dummy_389 f) from (by
                                        unfold nb095_alpha_dummy_389;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0556 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_385 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_385;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0554 D R S_cls E)
                                                  0)))) (show f ≠ (nb095_alpha_dummy_388 f) from
                                        (by
                                          unfold nb095_alpha_dummy_388;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0556 f) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_391 D R S_cls E) from (by
          unfold nb095_alpha_dummy_391;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0555 D R S_cls E)
                  0)))) (show f ≠ (nb095_alpha_dummy_392 f) from (by
          unfold nb095_alpha_dummy_392;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0557 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_383 D R S_cls E) from (by
          unfold nb095_alpha_dummy_383;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0552 D R S_cls E)
                  0)))) (show f ≠ (nb095_alpha_dummy_384 f) from (by
          unfold nb095_alpha_dummy_384;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0553 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_381 D R S_cls E) from (by
          unfold nb095_alpha_dummy_381;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0550 D R S_cls
                    E)
                  0)))) (show f ≠ (nb095_alpha_dummy_382 f) from (by
          unfold nb095_alpha_dummy_382;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0551 f) 0)))) (TAlphaVar.there (freshVar_injective
        ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_u (TAlphaVar.there
        (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_x
        (TAlphaVar.here _ _ _))))))))))))))))))))))))

@[expose]
noncomputable def nb095_split_alpha_0050 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_549 D R S_cls E), (nb095_alpha_dummy_550 f)),
        ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_383 D R S_cls E), (nb095_alpha_dummy_384 f)),
        ((nb095_alpha_dummy_381 D R S_cls E), (nb095_alpha_dummy_382 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_549 D R S_cls E))
          (Class.cab (nb095_alpha_dummy_543 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_549 D R S_cls E))
            (Class.cab (nb095_alpha_dummy_543 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_550 f))
          (Class.cab (nb095_alpha_dummy_545 f)
            (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_390 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_546 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_550 f))
            (Class.cab (nb095_alpha_dummy_545 f)
              (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_390 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_546 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_387 D R S_cls E) ≠
                      (nb095_alpha_dummy_544 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_544;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E) 1))))
                  (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_546 f) from (by
                      unfold nb095_alpha_dummy_546;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0564 f) 1))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_387 D R S_cls E) ≠
                        (nb095_alpha_dummy_543 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_543;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E) 0))))
                    (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_545 f) from (by
                        unfold nb095_alpha_dummy_545;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0564 f) 0)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_387 D R S_cls E) ≠
                          (nb095_alpha_dummy_549 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_549;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0566 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_550 f) from (by
                          unfold nb095_alpha_dummy_550;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0567 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_387 D R S_cls E) ≠
                            (nb095_alpha_dummy_547 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_547;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0563 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_548 f) from (by
                            unfold nb095_alpha_dummy_548;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0565 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_390 f))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_389 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_544 D R S_cls E) ≠
                              (nb095_alpha_dummy_551 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_551;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0568 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_553 f) from (by
                              unfold nb095_alpha_dummy_553;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0569 f) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_544 D R S_cls E) ≠
                                (nb095_alpha_dummy_552 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_552;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0568 D R S_cls E) 1))))
                            (show (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_554 f) from (by
                                unfold nb095_alpha_dummy_554;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0569 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_544 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095_alpha_dummy_546 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_551 D R S_cls E) ≠
        (nb095_alpha_dummy_558 D R S_cls E) from (by
          unfold nb095_alpha_dummy_558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R S_cls
                    E)
                  1)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_561 f) from (by
          unfold nb095_alpha_dummy_561;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_551 D R S_cls E) ≠ (nb095_alpha_dummy_557 D R S_cls E) from (by
          unfold nb095_alpha_dummy_557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_560 f) from (by
          unfold nb095_alpha_dummy_560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_551 D R S_cls E) ≠ (nb095_alpha_dummy_555 D R S_cls E) from (by
          unfold nb095_alpha_dummy_555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0570 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from (by
          unfold nb095_alpha_dummy_556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0571 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_559 D R S_cls E), (nb095_alpha_dummy_562 f)),
        ((nb095_alpha_dummy_558 D R S_cls E), (nb095_alpha_dummy_561 f)),
        ((nb095_alpha_dummy_557 D R S_cls E), (nb095_alpha_dummy_560 f)),
        ((nb095_alpha_dummy_555 D R S_cls E), (nb095_alpha_dummy_556 f)),
        ((nb095_alpha_dummy_551 D R S_cls E), (nb095_alpha_dummy_553 f)),
        ((nb095_alpha_dummy_552 D R S_cls E), (nb095_alpha_dummy_554 f)),
        ((nb095_alpha_dummy_544 D R S_cls E), (nb095_alpha_dummy_546 f)),
        ((nb095_alpha_dummy_543 D R S_cls E), (nb095_alpha_dummy_545 f)),
        ((nb095_alpha_dummy_549 D R S_cls E), (nb095_alpha_dummy_550 f)),
        ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_383 D R S_cls E), (nb095_alpha_dummy_384 f)),
        ((nb095_alpha_dummy_381 D R S_cls E), (nb095_alpha_dummy_382 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_558
        D R S_cls E) ≠ (nb095_alpha_dummy_565 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_559 D R S_cls E), (nb095_alpha_dummy_562 f)),
        ((nb095_alpha_dummy_558 D R S_cls E), (nb095_alpha_dummy_561 f)),
        ((nb095_alpha_dummy_557 D R S_cls E), (nb095_alpha_dummy_560 f)),
        ((nb095_alpha_dummy_555 D R S_cls E), (nb095_alpha_dummy_556 f)),
        ((nb095_alpha_dummy_551 D R S_cls E), (nb095_alpha_dummy_553 f)),
        ((nb095_alpha_dummy_552 D R S_cls E), (nb095_alpha_dummy_554 f)),
        ((nb095_alpha_dummy_544 D R S_cls E), (nb095_alpha_dummy_546 f)),
        ((nb095_alpha_dummy_543 D R S_cls E), (nb095_alpha_dummy_545 f)),
        ((nb095_alpha_dummy_549 D R S_cls E), (nb095_alpha_dummy_550 f)),
        ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_383 D R S_cls E), (nb095_alpha_dummy_384 f)),
        ((nb095_alpha_dummy_381 D R S_cls E), (nb095_alpha_dummy_382 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_569
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_570 f) from (by
          unfold
            nb095_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_569
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_570 f) from (by
          unfold
            nb095_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_559
        D R S_cls E) ≠ (nb095_alpha_dummy_571 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_572 f) from (by
          unfold
            nb095_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_559
        D R S_cls E) ≠ (nb095_alpha_dummy_571 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_572 f) from (by
          unfold
            nb095_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_551 D R S_cls E) ≠
                                        (nb095_alpha_dummy_555 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_555;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from
                                      (by
                                        unfold nb095_alpha_dummy_556;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0571 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_555 D R S_cls E),
                                      (nb095_alpha_dummy_556 f)),
                                    ((nb095_alpha_dummy_551 D R S_cls E),
                                      (nb095_alpha_dummy_553 f)),
                                    ((nb095_alpha_dummy_552 D R S_cls E),
                                      (nb095_alpha_dummy_554 f)),
                                    ((nb095_alpha_dummy_544 D R S_cls E),
                                      (nb095_alpha_dummy_546 f)),
                                    ((nb095_alpha_dummy_543 D R S_cls E),
                                      (nb095_alpha_dummy_545 f)),
                                    ((nb095_alpha_dummy_549 D R S_cls E),
                                      (nb095_alpha_dummy_550 f)),
                                    ((nb095_alpha_dummy_547 D R S_cls E),
                                      (nb095_alpha_dummy_548 f)),
                                    ((nb095_alpha_dummy_387 D R S_cls E),
                                      (nb095_alpha_dummy_390 f)),
                                    ((nb095_alpha_dummy_386 D R S_cls E),
                                      (nb095_alpha_dummy_389 f)),
                                    ((nb095_alpha_dummy_385 D R S_cls E),
                                      (nb095_alpha_dummy_388 f)),
                                    ((nb095_alpha_dummy_391 D R S_cls E),
                                      (nb095_alpha_dummy_392 f)),
                                    ((nb095_alpha_dummy_383 D R S_cls E),
                                      (nb095_alpha_dummy_384 f)),
                                    ((nb095_alpha_dummy_381 D R S_cls E),
                                      (nb095_alpha_dummy_382 f)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_551 D R S_cls E) ≠
                                      (nb095_alpha_dummy_555 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_555;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from
                                    (by
                                      unfold nb095_alpha_dummy_556;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0571 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_551 D R S_cls E) ≠
                                        (nb095_alpha_dummy_555 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_555;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from
                                      (by
                                        unfold nb095_alpha_dummy_556;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0571 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_555 D R S_cls E),
                                      (nb095_alpha_dummy_556 f)),
                                    ((nb095_alpha_dummy_551 D R S_cls E),
                                      (nb095_alpha_dummy_553 f)),
                                    ((nb095_alpha_dummy_552 D R S_cls E),
                                      (nb095_alpha_dummy_554 f)),
                                    ((nb095_alpha_dummy_544 D R S_cls E),
                                      (nb095_alpha_dummy_546 f)),
                                    ((nb095_alpha_dummy_543 D R S_cls E),
                                      (nb095_alpha_dummy_545 f)),
                                    ((nb095_alpha_dummy_549 D R S_cls E),
                                      (nb095_alpha_dummy_550 f)),
                                    ((nb095_alpha_dummy_547 D R S_cls E),
                                      (nb095_alpha_dummy_548 f)),
                                    ((nb095_alpha_dummy_387 D R S_cls E),
                                      (nb095_alpha_dummy_390 f)),
                                    ((nb095_alpha_dummy_386 D R S_cls E),
                                      (nb095_alpha_dummy_389 f)),
                                    ((nb095_alpha_dummy_385 D R S_cls E),
                                      (nb095_alpha_dummy_388 f)),
                                    ((nb095_alpha_dummy_391 D R S_cls E),
                                      (nb095_alpha_dummy_392 f)),
                                    ((nb095_alpha_dummy_383 D R S_cls E),
                                      (nb095_alpha_dummy_384 f)),
                                    ((nb095_alpha_dummy_381 D R S_cls E),
                                      (nb095_alpha_dummy_382 f)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095_alpha_dummy_387 D R S_cls E) ≠
                        (nb095_alpha_dummy_544 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_544;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E) 1))))
                    (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_546 f) from (by
                        unfold nb095_alpha_dummy_546;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0564 f) 1)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_387 D R S_cls E) ≠
                          (nb095_alpha_dummy_543 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_543;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_545 f) from (by
                          unfold nb095_alpha_dummy_545;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0564 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_387 D R S_cls E) ≠
                            (nb095_alpha_dummy_549 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_549;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0566 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_550 f) from (by
                            unfold nb095_alpha_dummy_550;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0567 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_387 D R S_cls E) ≠
                              (nb095_alpha_dummy_547 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_547;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0563 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_548 f) from (by
                              unfold nb095_alpha_dummy_548;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0565 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_390 f))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_389 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_544 D R S_cls E) ≠
                                (nb095_alpha_dummy_551 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_551;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0568 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_553 f) from (by
                                unfold nb095_alpha_dummy_553;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0569 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_544 D R S_cls E) ≠
                                  (nb095_alpha_dummy_552 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_552;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0568 D R S_cls E) 1))))
                              (show (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_554 f) from
                                (by
                                  unfold nb095_alpha_dummy_554;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0569 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_544 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_546 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_551 D R S_cls E) ≠ (nb095_alpha_dummy_558 D R S_cls E) from (by
          unfold nb095_alpha_dummy_558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_561 f) from (by
          unfold nb095_alpha_dummy_561;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_551 D R S_cls E) ≠ (nb095_alpha_dummy_557 D R S_cls E) from (by
          unfold nb095_alpha_dummy_557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_560 f) from (by
          unfold nb095_alpha_dummy_560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_551 D R S_cls E) ≠
        (nb095_alpha_dummy_555 D R S_cls E) from (by
          unfold nb095_alpha_dummy_555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0570 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from (by
          unfold nb095_alpha_dummy_556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0571 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_559 D R S_cls E), (nb095_alpha_dummy_562 f)),
        ((nb095_alpha_dummy_558 D R S_cls E), (nb095_alpha_dummy_561 f)),
        ((nb095_alpha_dummy_557 D R S_cls E), (nb095_alpha_dummy_560 f)),
        ((nb095_alpha_dummy_555 D R S_cls E), (nb095_alpha_dummy_556 f)),
        ((nb095_alpha_dummy_551 D R S_cls E), (nb095_alpha_dummy_553 f)),
        ((nb095_alpha_dummy_552 D R S_cls E), (nb095_alpha_dummy_554 f)),
        ((nb095_alpha_dummy_544 D R S_cls E), (nb095_alpha_dummy_546 f)),
        ((nb095_alpha_dummy_543 D R S_cls E), (nb095_alpha_dummy_545 f)),
        ((nb095_alpha_dummy_549 D R S_cls E), (nb095_alpha_dummy_550 f)),
        ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_383 D R S_cls E), (nb095_alpha_dummy_384 f)),
        ((nb095_alpha_dummy_381 D R S_cls E), (nb095_alpha_dummy_382 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_558
        D R S_cls E) ≠ (nb095_alpha_dummy_565 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_559 D R S_cls E), (nb095_alpha_dummy_562 f)),
        ((nb095_alpha_dummy_558 D R S_cls E), (nb095_alpha_dummy_561 f)),
        ((nb095_alpha_dummy_557 D R S_cls E), (nb095_alpha_dummy_560 f)),
        ((nb095_alpha_dummy_555 D R S_cls E), (nb095_alpha_dummy_556 f)),
        ((nb095_alpha_dummy_551 D R S_cls E), (nb095_alpha_dummy_553 f)),
        ((nb095_alpha_dummy_552 D R S_cls E), (nb095_alpha_dummy_554 f)),
        ((nb095_alpha_dummy_544 D R S_cls E), (nb095_alpha_dummy_546 f)),
        ((nb095_alpha_dummy_543 D R S_cls E), (nb095_alpha_dummy_545 f)),
        ((nb095_alpha_dummy_549 D R S_cls E), (nb095_alpha_dummy_550 f)),
        ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_383 D R S_cls E), (nb095_alpha_dummy_384 f)),
        ((nb095_alpha_dummy_381 D R S_cls E), (nb095_alpha_dummy_382 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_569
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_570 f) from (by
          unfold
            nb095_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_569
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_570 f) from (by
          unfold
            nb095_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_559
        D R S_cls E) ≠ (nb095_alpha_dummy_571 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_572 f) from (by
          unfold
            nb095_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_559
        D R S_cls E) ≠ (nb095_alpha_dummy_571 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_572 f) from (by
          unfold
            nb095_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_551 D R S_cls E) ≠
        (nb095_alpha_dummy_555 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_555;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0570 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_553 f) ≠
        (nb095_alpha_dummy_556 f) from (by
                                          unfold nb095_alpha_dummy_556;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0571 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_555 D R S_cls E),
                                        (nb095_alpha_dummy_556 f)),
                                      ((nb095_alpha_dummy_551 D R S_cls E),
                                        (nb095_alpha_dummy_553 f)),
                                      ((nb095_alpha_dummy_552 D R S_cls E),
                                        (nb095_alpha_dummy_554 f)),
                                      ((nb095_alpha_dummy_544 D R S_cls E),
                                        (nb095_alpha_dummy_546 f)),
                                      ((nb095_alpha_dummy_543 D R S_cls E),
                                        (nb095_alpha_dummy_545 f)),
                                      ((nb095_alpha_dummy_549 D R S_cls E),
                                        (nb095_alpha_dummy_550 f)),
                                      ((nb095_alpha_dummy_547 D R S_cls E),
                                        (nb095_alpha_dummy_548 f)),
                                      ((nb095_alpha_dummy_387 D R S_cls E),
                                        (nb095_alpha_dummy_390 f)),
                                      ((nb095_alpha_dummy_386 D R S_cls E),
                                        (nb095_alpha_dummy_389 f)),
                                      ((nb095_alpha_dummy_385 D R S_cls E),
                                        (nb095_alpha_dummy_388 f)),
                                      ((nb095_alpha_dummy_391 D R S_cls E),
                                        (nb095_alpha_dummy_392 f)),
                                      ((nb095_alpha_dummy_383 D R S_cls E),
                                        (nb095_alpha_dummy_384 f)),
                                      ((nb095_alpha_dummy_381 D R S_cls E),
                                        (nb095_alpha_dummy_382 f)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_551 D R S_cls E) ≠
                                        (nb095_alpha_dummy_555 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_555;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from
                                      (by
                                        unfold nb095_alpha_dummy_556;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0571 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_551 D R S_cls E) ≠
        (nb095_alpha_dummy_555 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_555;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0570 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_553 f) ≠
        (nb095_alpha_dummy_556 f) from (by
                                          unfold nb095_alpha_dummy_556;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0571 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_555 D R S_cls E),
                                        (nb095_alpha_dummy_556 f)),
                                      ((nb095_alpha_dummy_551 D R S_cls E),
                                        (nb095_alpha_dummy_553 f)),
                                      ((nb095_alpha_dummy_552 D R S_cls E),
                                        (nb095_alpha_dummy_554 f)),
                                      ((nb095_alpha_dummy_544 D R S_cls E),
                                        (nb095_alpha_dummy_546 f)),
                                      ((nb095_alpha_dummy_543 D R S_cls E),
                                        (nb095_alpha_dummy_545 f)),
                                      ((nb095_alpha_dummy_549 D R S_cls E),
                                        (nb095_alpha_dummy_550 f)),
                                      ((nb095_alpha_dummy_547 D R S_cls E),
                                        (nb095_alpha_dummy_548 f)),
                                      ((nb095_alpha_dummy_387 D R S_cls E),
                                        (nb095_alpha_dummy_390 f)),
                                      ((nb095_alpha_dummy_386 D R S_cls E),
                                        (nb095_alpha_dummy_389 f)),
                                      ((nb095_alpha_dummy_385 D R S_cls E),
                                        (nb095_alpha_dummy_388 f)),
                                      ((nb095_alpha_dummy_391 D R S_cls E),
                                        (nb095_alpha_dummy_392 f)),
                                      ((nb095_alpha_dummy_383 D R S_cls E),
                                        (nb095_alpha_dummy_384 f)),
                                      ((nb095_alpha_dummy_381 D R S_cls E),
                                        (nb095_alpha_dummy_382 f)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

@[expose]
noncomputable def nb095_split_alpha_0051 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_575 D R S_cls E), (nb095_alpha_dummy_576 f)),
        ((nb095_alpha_dummy_544 D R S_cls E), (nb095_alpha_dummy_546 f)),
        ((nb095_alpha_dummy_543 D R S_cls E), (nb095_alpha_dummy_545 f)),
        ((nb095_alpha_dummy_573 D R S_cls E), (nb095_alpha_dummy_574 f)),
        ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_383 D R S_cls E), (nb095_alpha_dummy_384 f)),
        ((nb095_alpha_dummy_381 D R S_cls E), (nb095_alpha_dummy_382 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.classMem (Class.cv (nb095_alpha_dummy_575 D R S_cls E))
        (syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))))
      (Wff.classMem (Class.cv (nb095_alpha_dummy_576 f))
        (syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_546 f))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095_alpha_dummy_544 D R S_cls E) ≠
                            (nb095_alpha_dummy_551 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_551;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0568 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_553 f) from (by
                            unfold nb095_alpha_dummy_553;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0569 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_544 D R S_cls E) ≠
                              (nb095_alpha_dummy_552 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_552;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0568 D R S_cls E)
                                      1))))
                          (show (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_554 f) from (by
                              unfold nb095_alpha_dummy_554;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0569 f) 1))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_544 D R S_cls E) ≠
                                (nb095_alpha_dummy_577 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_577;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0598 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_578 f) from (by
                                unfold nb095_alpha_dummy_578;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0599 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_544 D R S_cls E) ≠
                                  (nb095_alpha_dummy_575 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_575;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0596 D R S_cls E) 0))))
                              (show (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_576 f) from
                                (by
                                  unfold nb095_alpha_dummy_576;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0597 f) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb095_alpha_dummy_544 D R S_cls E))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb095_alpha_dummy_546 f))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095_alpha_dummy_551 D R S_cls E) ≠ (nb095_alpha_dummy_558 D R S_cls E) from (by
          unfold nb095_alpha_dummy_558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_561 f) from (by
          unfold nb095_alpha_dummy_561;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_551 D R S_cls E) ≠ (nb095_alpha_dummy_557 D R S_cls E) from (by
          unfold nb095_alpha_dummy_557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_560 f) from (by
          unfold nb095_alpha_dummy_560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_551 D R S_cls E) ≠ (nb095_alpha_dummy_555 D R S_cls E) from (by
          unfold nb095_alpha_dummy_555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0570 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from (by
          unfold nb095_alpha_dummy_556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0571 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_559 D R S_cls E), (nb095_alpha_dummy_562 f)),
        ((nb095_alpha_dummy_558 D R S_cls E), (nb095_alpha_dummy_561 f)),
        ((nb095_alpha_dummy_557 D R S_cls E), (nb095_alpha_dummy_560 f)),
        ((nb095_alpha_dummy_555 D R S_cls E), (nb095_alpha_dummy_556 f)),
        ((nb095_alpha_dummy_551 D R S_cls E), (nb095_alpha_dummy_553 f)),
        ((nb095_alpha_dummy_552 D R S_cls E), (nb095_alpha_dummy_554 f)),
        ((nb095_alpha_dummy_577 D R S_cls E), (nb095_alpha_dummy_578 f)),
        ((nb095_alpha_dummy_575 D R S_cls E), (nb095_alpha_dummy_576 f)),
        ((nb095_alpha_dummy_544 D R S_cls E), (nb095_alpha_dummy_546 f)),
        ((nb095_alpha_dummy_543 D R S_cls E), (nb095_alpha_dummy_545 f)),
        ((nb095_alpha_dummy_573 D R S_cls E), (nb095_alpha_dummy_574 f)),
        ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_383 D R S_cls E), (nb095_alpha_dummy_384 f)),
        ((nb095_alpha_dummy_381 D R S_cls E), (nb095_alpha_dummy_382 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
                                        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_559 D R S_cls E), (nb095_alpha_dummy_562 f)),
        ((nb095_alpha_dummy_558 D R S_cls E), (nb095_alpha_dummy_561 f)),
        ((nb095_alpha_dummy_557 D R S_cls E), (nb095_alpha_dummy_560 f)),
        ((nb095_alpha_dummy_555 D R S_cls E), (nb095_alpha_dummy_556 f)),
        ((nb095_alpha_dummy_551 D R S_cls E), (nb095_alpha_dummy_553 f)),
        ((nb095_alpha_dummy_552 D R S_cls E), (nb095_alpha_dummy_554 f)),
        ((nb095_alpha_dummy_577 D R S_cls E), (nb095_alpha_dummy_578 f)),
        ((nb095_alpha_dummy_575 D R S_cls E), (nb095_alpha_dummy_576 f)),
        ((nb095_alpha_dummy_544 D R S_cls E), (nb095_alpha_dummy_546 f)),
        ((nb095_alpha_dummy_543 D R S_cls E), (nb095_alpha_dummy_545 f)),
        ((nb095_alpha_dummy_573 D R S_cls E), (nb095_alpha_dummy_574 f)),
        ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_383 D R S_cls E), (nb095_alpha_dummy_384 f)),
        ((nb095_alpha_dummy_381 D R S_cls E), (nb095_alpha_dummy_382 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_558 D
        R S_cls E) ≠ (nb095_alpha_dummy_569 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_570 f) from (by
          unfold
            nb095_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_569
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_570 f) from (by
          unfold
            nb095_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_559 D
        R S_cls E) ≠ (nb095_alpha_dummy_571 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_572 f) from (by
          unfold
            nb095_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_559 D
        R S_cls E) ≠ (nb095_alpha_dummy_571 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_572 f) from (by
          unfold
            nb095_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_551 D R S_cls E) ≠
                                      (nb095_alpha_dummy_555 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_555;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from
                                    (by
                                      unfold nb095_alpha_dummy_556;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0571 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_555 D R S_cls E),
                                    (nb095_alpha_dummy_556 f)),
                                  ((nb095_alpha_dummy_551 D R S_cls E),
                                    (nb095_alpha_dummy_553 f)),
                                  ((nb095_alpha_dummy_552 D R S_cls E),
                                    (nb095_alpha_dummy_554 f)),
                                  ((nb095_alpha_dummy_577 D R S_cls E),
                                    (nb095_alpha_dummy_578 f)),
                                  ((nb095_alpha_dummy_575 D R S_cls E),
                                    (nb095_alpha_dummy_576 f)),
                                  ((nb095_alpha_dummy_544 D R S_cls E),
                                    (nb095_alpha_dummy_546 f)),
                                  ((nb095_alpha_dummy_543 D R S_cls E),
                                    (nb095_alpha_dummy_545 f)),
                                  ((nb095_alpha_dummy_573 D R S_cls E),
                                    (nb095_alpha_dummy_574 f)),
                                  ((nb095_alpha_dummy_547 D R S_cls E),
                                    (nb095_alpha_dummy_548 f)),
                                  ((nb095_alpha_dummy_387 D R S_cls E),
                                    (nb095_alpha_dummy_390 f)),
                                  ((nb095_alpha_dummy_386 D R S_cls E),
                                    (nb095_alpha_dummy_389 f)),
                                  ((nb095_alpha_dummy_385 D R S_cls E),
                                    (nb095_alpha_dummy_388 f)),
                                  ((nb095_alpha_dummy_391 D R S_cls E),
                                    (nb095_alpha_dummy_392 f)),
                                  ((nb095_alpha_dummy_383 D R S_cls E),
                                    (nb095_alpha_dummy_384 f)),
                                  ((nb095_alpha_dummy_381 D R S_cls E),
                                    (nb095_alpha_dummy_382 f)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb095_alpha_dummy_551 D R S_cls E) ≠
                                    (nb095_alpha_dummy_555 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_555;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from (by
                                    unfold nb095_alpha_dummy_556;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0571 f)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_551 D R S_cls E) ≠
                                      (nb095_alpha_dummy_555 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_555;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from
                                    (by
                                      unfold nb095_alpha_dummy_556;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0571 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_555 D R S_cls E),
                                    (nb095_alpha_dummy_556 f)),
                                  ((nb095_alpha_dummy_551 D R S_cls E),
                                    (nb095_alpha_dummy_553 f)),
                                  ((nb095_alpha_dummy_552 D R S_cls E),
                                    (nb095_alpha_dummy_554 f)),
                                  ((nb095_alpha_dummy_577 D R S_cls E),
                                    (nb095_alpha_dummy_578 f)),
                                  ((nb095_alpha_dummy_575 D R S_cls E),
                                    (nb095_alpha_dummy_576 f)),
                                  ((nb095_alpha_dummy_544 D R S_cls E),
                                    (nb095_alpha_dummy_546 f)),
                                  ((nb095_alpha_dummy_543 D R S_cls E),
                                    (nb095_alpha_dummy_545 f)),
                                  ((nb095_alpha_dummy_573 D R S_cls E),
                                    (nb095_alpha_dummy_574 f)),
                                  ((nb095_alpha_dummy_547 D R S_cls E),
                                    (nb095_alpha_dummy_548 f)),
                                  ((nb095_alpha_dummy_387 D R S_cls E),
                                    (nb095_alpha_dummy_390 f)),
                                  ((nb095_alpha_dummy_386 D R S_cls E),
                                    (nb095_alpha_dummy_389 f)),
                                  ((nb095_alpha_dummy_385 D R S_cls E),
                                    (nb095_alpha_dummy_388 f)),
                                  ((nb095_alpha_dummy_391 D R S_cls E),
                                    (nb095_alpha_dummy_392 f)),
                                  ((nb095_alpha_dummy_383 D R S_cls E),
                                    (nb095_alpha_dummy_384 f)),
                                  ((nb095_alpha_dummy_381 D R S_cls E),
                                    (nb095_alpha_dummy_382 f)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095_alpha_dummy_544 D R S_cls E) ≠
                            (nb095_alpha_dummy_551 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_551;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0568 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_553 f) from (by
                            unfold nb095_alpha_dummy_553;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0569 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_544 D R S_cls E) ≠
                              (nb095_alpha_dummy_552 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_552;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0568 D R S_cls E)
                                      1))))
                          (show (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_554 f) from (by
                              unfold nb095_alpha_dummy_554;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0569 f) 1))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_544 D R S_cls E) ≠
                                (nb095_alpha_dummy_577 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_577;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0598 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_578 f) from (by
                                unfold nb095_alpha_dummy_578;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0599 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_544 D R S_cls E) ≠
                                  (nb095_alpha_dummy_575 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_575;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0596 D R S_cls E) 0))))
                              (show (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_576 f) from
                                (by
                                  unfold nb095_alpha_dummy_576;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0597 f) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb095_alpha_dummy_544 D R S_cls E))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb095_alpha_dummy_546 f))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095_alpha_dummy_551 D R S_cls E) ≠ (nb095_alpha_dummy_558 D R S_cls E) from (by
          unfold nb095_alpha_dummy_558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_561 f) from (by
          unfold nb095_alpha_dummy_561;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_551 D R S_cls E) ≠ (nb095_alpha_dummy_557 D R S_cls E) from (by
          unfold nb095_alpha_dummy_557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_560 f) from (by
          unfold nb095_alpha_dummy_560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_551 D R S_cls E) ≠ (nb095_alpha_dummy_555 D R S_cls E) from (by
          unfold nb095_alpha_dummy_555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0570 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from (by
          unfold nb095_alpha_dummy_556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0571 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_559 D R S_cls E), (nb095_alpha_dummy_562 f)),
        ((nb095_alpha_dummy_558 D R S_cls E), (nb095_alpha_dummy_561 f)),
        ((nb095_alpha_dummy_557 D R S_cls E), (nb095_alpha_dummy_560 f)),
        ((nb095_alpha_dummy_555 D R S_cls E), (nb095_alpha_dummy_556 f)),
        ((nb095_alpha_dummy_551 D R S_cls E), (nb095_alpha_dummy_553 f)),
        ((nb095_alpha_dummy_552 D R S_cls E), (nb095_alpha_dummy_554 f)),
        ((nb095_alpha_dummy_577 D R S_cls E), (nb095_alpha_dummy_578 f)),
        ((nb095_alpha_dummy_575 D R S_cls E), (nb095_alpha_dummy_576 f)),
        ((nb095_alpha_dummy_544 D R S_cls E), (nb095_alpha_dummy_546 f)),
        ((nb095_alpha_dummy_543 D R S_cls E), (nb095_alpha_dummy_545 f)),
        ((nb095_alpha_dummy_573 D R S_cls E), (nb095_alpha_dummy_574 f)),
        ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_383 D R S_cls E), (nb095_alpha_dummy_384 f)),
        ((nb095_alpha_dummy_381 D R S_cls E), (nb095_alpha_dummy_382 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
                                        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_559 D R S_cls E), (nb095_alpha_dummy_562 f)),
        ((nb095_alpha_dummy_558 D R S_cls E), (nb095_alpha_dummy_561 f)),
        ((nb095_alpha_dummy_557 D R S_cls E), (nb095_alpha_dummy_560 f)),
        ((nb095_alpha_dummy_555 D R S_cls E), (nb095_alpha_dummy_556 f)),
        ((nb095_alpha_dummy_551 D R S_cls E), (nb095_alpha_dummy_553 f)),
        ((nb095_alpha_dummy_552 D R S_cls E), (nb095_alpha_dummy_554 f)),
        ((nb095_alpha_dummy_577 D R S_cls E), (nb095_alpha_dummy_578 f)),
        ((nb095_alpha_dummy_575 D R S_cls E), (nb095_alpha_dummy_576 f)),
        ((nb095_alpha_dummy_544 D R S_cls E), (nb095_alpha_dummy_546 f)),
        ((nb095_alpha_dummy_543 D R S_cls E), (nb095_alpha_dummy_545 f)),
        ((nb095_alpha_dummy_573 D R S_cls E), (nb095_alpha_dummy_574 f)),
        ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_383 D R S_cls E), (nb095_alpha_dummy_384 f)),
        ((nb095_alpha_dummy_381 D R S_cls E), (nb095_alpha_dummy_382 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_558 D
        R S_cls E) ≠ (nb095_alpha_dummy_569 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_570 f) from (by
          unfold
            nb095_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_569
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_570 f) from (by
          unfold
            nb095_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_559 D
        R S_cls E) ≠ (nb095_alpha_dummy_571 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_572 f) from (by
          unfold
            nb095_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_559 D
        R S_cls E) ≠ (nb095_alpha_dummy_571 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_572 f) from (by
          unfold
            nb095_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_551 D R S_cls E) ≠
                                      (nb095_alpha_dummy_555 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_555;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from
                                    (by
                                      unfold nb095_alpha_dummy_556;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0571 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_555 D R S_cls E),
                                    (nb095_alpha_dummy_556 f)),
                                  ((nb095_alpha_dummy_551 D R S_cls E),
                                    (nb095_alpha_dummy_553 f)),
                                  ((nb095_alpha_dummy_552 D R S_cls E),
                                    (nb095_alpha_dummy_554 f)),
                                  ((nb095_alpha_dummy_577 D R S_cls E),
                                    (nb095_alpha_dummy_578 f)),
                                  ((nb095_alpha_dummy_575 D R S_cls E),
                                    (nb095_alpha_dummy_576 f)),
                                  ((nb095_alpha_dummy_544 D R S_cls E),
                                    (nb095_alpha_dummy_546 f)),
                                  ((nb095_alpha_dummy_543 D R S_cls E),
                                    (nb095_alpha_dummy_545 f)),
                                  ((nb095_alpha_dummy_573 D R S_cls E),
                                    (nb095_alpha_dummy_574 f)),
                                  ((nb095_alpha_dummy_547 D R S_cls E),
                                    (nb095_alpha_dummy_548 f)),
                                  ((nb095_alpha_dummy_387 D R S_cls E),
                                    (nb095_alpha_dummy_390 f)),
                                  ((nb095_alpha_dummy_386 D R S_cls E),
                                    (nb095_alpha_dummy_389 f)),
                                  ((nb095_alpha_dummy_385 D R S_cls E),
                                    (nb095_alpha_dummy_388 f)),
                                  ((nb095_alpha_dummy_391 D R S_cls E),
                                    (nb095_alpha_dummy_392 f)),
                                  ((nb095_alpha_dummy_383 D R S_cls E),
                                    (nb095_alpha_dummy_384 f)),
                                  ((nb095_alpha_dummy_381 D R S_cls E),
                                    (nb095_alpha_dummy_382 f)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb095_alpha_dummy_551 D R S_cls E) ≠
                                    (nb095_alpha_dummy_555 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_555;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from (by
                                    unfold nb095_alpha_dummy_556;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0571 f)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_551 D R S_cls E) ≠
                                      (nb095_alpha_dummy_555 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_555;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from
                                    (by
                                      unfold nb095_alpha_dummy_556;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0571 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_555 D R S_cls E),
                                    (nb095_alpha_dummy_556 f)),
                                  ((nb095_alpha_dummy_551 D R S_cls E),
                                    (nb095_alpha_dummy_553 f)),
                                  ((nb095_alpha_dummy_552 D R S_cls E),
                                    (nb095_alpha_dummy_554 f)),
                                  ((nb095_alpha_dummy_577 D R S_cls E),
                                    (nb095_alpha_dummy_578 f)),
                                  ((nb095_alpha_dummy_575 D R S_cls E),
                                    (nb095_alpha_dummy_576 f)),
                                  ((nb095_alpha_dummy_544 D R S_cls E),
                                    (nb095_alpha_dummy_546 f)),
                                  ((nb095_alpha_dummy_543 D R S_cls E),
                                    (nb095_alpha_dummy_545 f)),
                                  ((nb095_alpha_dummy_573 D R S_cls E),
                                    (nb095_alpha_dummy_574 f)),
                                  ((nb095_alpha_dummy_547 D R S_cls E),
                                    (nb095_alpha_dummy_548 f)),
                                  ((nb095_alpha_dummy_387 D R S_cls E),
                                    (nb095_alpha_dummy_390 f)),
                                  ((nb095_alpha_dummy_386 D R S_cls E),
                                    (nb095_alpha_dummy_389 f)),
                                  ((nb095_alpha_dummy_385 D R S_cls E),
                                    (nb095_alpha_dummy_388 f)),
                                  ((nb095_alpha_dummy_391 D R S_cls E),
                                    (nb095_alpha_dummy_392 f)),
                                  ((nb095_alpha_dummy_383 D R S_cls E),
                                    (nb095_alpha_dummy_384 f)),
                                  ((nb095_alpha_dummy_381 D R S_cls E),
                                    (nb095_alpha_dummy_382 f)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
