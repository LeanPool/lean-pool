/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block020

/-! NF weak partition development: NAR4C078C001Part069. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0039`. -/
@[expose]
noncomputable def nb078SplitAlpha0039 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy477), (nb078AlphaDummy478 g)),
        ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
        ((nb078AlphaDummy445), (nb078AlphaDummy447 g)),
        ((nb078AlphaDummy475), (nb078AlphaDummy476 g)),
        ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
        ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.classMem (Class.cv (nb078AlphaDummy477))
        (synCcompl (synCphi (Class.cv (nb078AlphaDummy446)))))
      (Wff.classMem (Class.cv (nb078AlphaDummy478 g))
        (synCcompl (synCphi (Class.cv (nb078AlphaDummy448 g))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb078AlphaDummy446) ≠ (nb078AlphaDummy453) from (by
                            unfold nb078AlphaDummy453;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0468) 0))))
                        (show (nb078AlphaDummy448 g) ≠ (nb078AlphaDummy455 g) from (by
                            unfold nb078AlphaDummy455;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0469 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy446) ≠ (nb078AlphaDummy454) from (by
                              unfold nb078AlphaDummy454;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0468) 1))))
                          (show (nb078AlphaDummy448 g) ≠ (nb078AlphaDummy456 g) from (by
                              unfold nb078AlphaDummy456;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0469 g) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy446) ≠ (nb078AlphaDummy479) from (by
                                unfold nb078AlphaDummy479;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0498) 0))))
                            (show (nb078AlphaDummy448 g) ≠ (nb078AlphaDummy480 g) from (by
                                unfold nb078AlphaDummy480;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0499 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy446) ≠ (nb078AlphaDummy477) from (by
                                  unfold nb078AlphaDummy477;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0496) 0))))
                              (show (nb078AlphaDummy448 g) ≠ (nb078AlphaDummy478 g) from
                                (by
                                  unfold nb078AlphaDummy478;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0497 g) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb078AlphaDummy446))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb078AlphaDummy448 g))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy453) ≠
        (nb078AlphaDummy460) from (by
          unfold nb078AlphaDummy460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0472) 1)))) (show (nb078AlphaDummy455 g) ≠
        (nb078AlphaDummy463 g) from (by
          unfold nb078AlphaDummy463;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0473 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy453) ≠ (nb078AlphaDummy459) from (by
          unfold nb078AlphaDummy459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0472) 0)))) (show (nb078AlphaDummy455 g) ≠
        (nb078AlphaDummy462 g) from (by
          unfold nb078AlphaDummy462;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0473 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy453) ≠ (nb078AlphaDummy457) from (by
          unfold nb078AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0470) 0)))) (show (nb078AlphaDummy455 g) ≠
        (nb078AlphaDummy458 g) from (by
          unfold nb078AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0471 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy461), (nb078AlphaDummy464 g)), ((nb078AlphaDummy460),
        (nb078AlphaDummy463 g)), ((nb078AlphaDummy459), (nb078AlphaDummy462 g)),
        ((nb078AlphaDummy457), (nb078AlphaDummy458 g)), ((nb078AlphaDummy453),
        (nb078AlphaDummy455 g)), ((nb078AlphaDummy454), (nb078AlphaDummy456 g)),
        ((nb078AlphaDummy479), (nb078AlphaDummy480 g)), ((nb078AlphaDummy477),
        (nb078AlphaDummy478 g)), ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
        ((nb078AlphaDummy445), (nb078AlphaDummy447 g)), ((nb078AlphaDummy475),
        (nb078AlphaDummy476 g)), ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)), ((nb078AlphaDummy288),
        (nb078AlphaDummy291 g)), ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)), ((nb078AlphaDummy285),
        (nb078AlphaDummy286 g)), ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy467) from (by
          unfold
            nb078AlphaDummy467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0476)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy468 g) from (by
          unfold
            nb078AlphaDummy468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0477
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy465)
        from (by
          unfold
            nb078AlphaDummy465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0474)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy466 g) from (by
          unfold
            nb078AlphaDummy466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0475
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy467)
        from (by
          unfold
            nb078AlphaDummy467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0480)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy468 g) from (by
          unfold
            nb078AlphaDummy468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0481
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy465)
        from (by
          unfold
            nb078AlphaDummy465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0478)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy466 g) from (by
          unfold
            nb078AlphaDummy466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0479
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy467) from (by
          unfold
            nb078AlphaDummy467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0476)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy468 g) from (by
          unfold
            nb078AlphaDummy468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0477
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy465)
        from (by
          unfold
            nb078AlphaDummy465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0474)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy466 g) from (by
          unfold
            nb078AlphaDummy466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0475
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy467)
        from (by
          unfold
            nb078AlphaDummy467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0480)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy468 g) from (by
          unfold
            nb078AlphaDummy468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0481
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy465)
        from (by
          unfold
            nb078AlphaDummy465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0478)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy466 g) from (by
          unfold
            nb078AlphaDummy466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0479
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy461), (nb078AlphaDummy464 g)), ((nb078AlphaDummy460),
        (nb078AlphaDummy463 g)), ((nb078AlphaDummy459), (nb078AlphaDummy462 g)),
        ((nb078AlphaDummy457), (nb078AlphaDummy458 g)), ((nb078AlphaDummy453),
        (nb078AlphaDummy455 g)), ((nb078AlphaDummy454), (nb078AlphaDummy456 g)),
        ((nb078AlphaDummy479), (nb078AlphaDummy480 g)), ((nb078AlphaDummy477),
        (nb078AlphaDummy478 g)), ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
        ((nb078AlphaDummy445), (nb078AlphaDummy447 g)), ((nb078AlphaDummy475),
        (nb078AlphaDummy476 g)), ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)), ((nb078AlphaDummy288),
        (nb078AlphaDummy291 g)), ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)), ((nb078AlphaDummy285),
        (nb078AlphaDummy286 g)), ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy453))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy471) from (by
          unfold
            nb078AlphaDummy471;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0484)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy472 g) from (by
          unfold
            nb078AlphaDummy472;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0485
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy469)
        from (by
          unfold
            nb078AlphaDummy469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0482)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy470 g) from (by
          unfold
            nb078AlphaDummy470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0483
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy471)
        from (by
          unfold
            nb078AlphaDummy471;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0484)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy472 g) from (by
          unfold
            nb078AlphaDummy472;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0485
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy469)
        from (by
          unfold
            nb078AlphaDummy469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0482)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy470 g) from (by
          unfold
            nb078AlphaDummy470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0483
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy473) from (by
          unfold
            nb078AlphaDummy473;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0488)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy474 g) from (by
          unfold
            nb078AlphaDummy474;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0489
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy469)
        from (by
          unfold
            nb078AlphaDummy469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0486)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy470 g) from (by
          unfold
            nb078AlphaDummy470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0487
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy461) ≠
        (nb078AlphaDummy473) from (by
          unfold
            nb078AlphaDummy473;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0488)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy474 g) from (by
          unfold
            nb078AlphaDummy474;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0489
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy469)
        from (by
          unfold
            nb078AlphaDummy469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0486)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy470 g) from (by
          unfold
            nb078AlphaDummy470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0487
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy453) ≠ (nb078AlphaDummy457) from
                                    (by
                                      unfold nb078AlphaDummy457;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0470)
                                              0)))) (show
                                    (nb078AlphaDummy455 g) ≠ (nb078AlphaDummy458 g) from
                                    (by
                                      unfold nb078AlphaDummy458;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0471 g)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb078AlphaDummy457), (nb078AlphaDummy458 g)),
                                  ((nb078AlphaDummy453), (nb078AlphaDummy455 g)),
                                  ((nb078AlphaDummy454), (nb078AlphaDummy456 g)),
                                  ((nb078AlphaDummy479), (nb078AlphaDummy480 g)),
                                  ((nb078AlphaDummy477), (nb078AlphaDummy478 g)),
                                  ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
                                  ((nb078AlphaDummy445), (nb078AlphaDummy447 g)),
                                  ((nb078AlphaDummy475), (nb078AlphaDummy476 g)),
                                  ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
                                  ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                  ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                  ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                  ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                  ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
                                  ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
                                  ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                  ((nb078AlphaDummy003), x)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078AlphaDummy453) ≠ (nb078AlphaDummy457) from (by
                                    unfold nb078AlphaDummy457;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0470) 0)))) (show
                                  (nb078AlphaDummy455 g) ≠ (nb078AlphaDummy458 g) from (by
                                    unfold nb078AlphaDummy458;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0471 g)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy453) ≠ (nb078AlphaDummy457) from
                                    (by
                                      unfold nb078AlphaDummy457;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0470)
                                              0)))) (show
                                    (nb078AlphaDummy455 g) ≠ (nb078AlphaDummy458 g) from
                                    (by
                                      unfold nb078AlphaDummy458;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0471 g)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb078AlphaDummy457), (nb078AlphaDummy458 g)),
                                  ((nb078AlphaDummy453), (nb078AlphaDummy455 g)),
                                  ((nb078AlphaDummy454), (nb078AlphaDummy456 g)),
                                  ((nb078AlphaDummy479), (nb078AlphaDummy480 g)),
                                  ((nb078AlphaDummy477), (nb078AlphaDummy478 g)),
                                  ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
                                  ((nb078AlphaDummy445), (nb078AlphaDummy447 g)),
                                  ((nb078AlphaDummy475), (nb078AlphaDummy476 g)),
                                  ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
                                  ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                  ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                  ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                  ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                  ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
                                  ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
                                  ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                  ((nb078AlphaDummy003), x)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb078AlphaDummy446) ≠ (nb078AlphaDummy453) from (by
                            unfold nb078AlphaDummy453;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0468) 0))))
                        (show (nb078AlphaDummy448 g) ≠ (nb078AlphaDummy455 g) from (by
                            unfold nb078AlphaDummy455;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0469 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy446) ≠ (nb078AlphaDummy454) from (by
                              unfold nb078AlphaDummy454;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0468) 1))))
                          (show (nb078AlphaDummy448 g) ≠ (nb078AlphaDummy456 g) from (by
                              unfold nb078AlphaDummy456;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0469 g) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy446) ≠ (nb078AlphaDummy479) from (by
                                unfold nb078AlphaDummy479;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0498) 0))))
                            (show (nb078AlphaDummy448 g) ≠ (nb078AlphaDummy480 g) from (by
                                unfold nb078AlphaDummy480;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0499 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy446) ≠ (nb078AlphaDummy477) from (by
                                  unfold nb078AlphaDummy477;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0496) 0))))
                              (show (nb078AlphaDummy448 g) ≠ (nb078AlphaDummy478 g) from
                                (by
                                  unfold nb078AlphaDummy478;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0497 g) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb078AlphaDummy446))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb078AlphaDummy448 g))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy453) ≠
        (nb078AlphaDummy460) from (by
          unfold nb078AlphaDummy460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0472) 1)))) (show (nb078AlphaDummy455 g) ≠
        (nb078AlphaDummy463 g) from (by
          unfold nb078AlphaDummy463;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0473 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy453) ≠ (nb078AlphaDummy459) from (by
          unfold nb078AlphaDummy459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0472) 0)))) (show (nb078AlphaDummy455 g) ≠
        (nb078AlphaDummy462 g) from (by
          unfold nb078AlphaDummy462;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0473 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy453) ≠ (nb078AlphaDummy457) from (by
          unfold nb078AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0470) 0)))) (show (nb078AlphaDummy455 g) ≠
        (nb078AlphaDummy458 g) from (by
          unfold nb078AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0471 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy461), (nb078AlphaDummy464 g)), ((nb078AlphaDummy460),
        (nb078AlphaDummy463 g)), ((nb078AlphaDummy459), (nb078AlphaDummy462 g)),
        ((nb078AlphaDummy457), (nb078AlphaDummy458 g)), ((nb078AlphaDummy453),
        (nb078AlphaDummy455 g)), ((nb078AlphaDummy454), (nb078AlphaDummy456 g)),
        ((nb078AlphaDummy479), (nb078AlphaDummy480 g)), ((nb078AlphaDummy477),
        (nb078AlphaDummy478 g)), ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
        ((nb078AlphaDummy445), (nb078AlphaDummy447 g)), ((nb078AlphaDummy475),
        (nb078AlphaDummy476 g)), ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)), ((nb078AlphaDummy288),
        (nb078AlphaDummy291 g)), ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)), ((nb078AlphaDummy285),
        (nb078AlphaDummy286 g)), ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy467) from (by
          unfold
            nb078AlphaDummy467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0476)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy468 g) from (by
          unfold
            nb078AlphaDummy468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0477
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy465)
        from (by
          unfold
            nb078AlphaDummy465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0474)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy466 g) from (by
          unfold
            nb078AlphaDummy466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0475
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy467)
        from (by
          unfold
            nb078AlphaDummy467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0480)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy468 g) from (by
          unfold
            nb078AlphaDummy468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0481
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy465)
        from (by
          unfold
            nb078AlphaDummy465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0478)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy466 g) from (by
          unfold
            nb078AlphaDummy466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0479
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy467) from (by
          unfold
            nb078AlphaDummy467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0476)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy468 g) from (by
          unfold
            nb078AlphaDummy468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0477
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy465)
        from (by
          unfold
            nb078AlphaDummy465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0474)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy466 g) from (by
          unfold
            nb078AlphaDummy466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0475
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy467)
        from (by
          unfold
            nb078AlphaDummy467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0480)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy468 g) from (by
          unfold
            nb078AlphaDummy468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0481
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy465)
        from (by
          unfold
            nb078AlphaDummy465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0478)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy466 g) from (by
          unfold
            nb078AlphaDummy466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0479
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy461), (nb078AlphaDummy464 g)), ((nb078AlphaDummy460),
        (nb078AlphaDummy463 g)), ((nb078AlphaDummy459), (nb078AlphaDummy462 g)),
        ((nb078AlphaDummy457), (nb078AlphaDummy458 g)), ((nb078AlphaDummy453),
        (nb078AlphaDummy455 g)), ((nb078AlphaDummy454), (nb078AlphaDummy456 g)),
        ((nb078AlphaDummy479), (nb078AlphaDummy480 g)), ((nb078AlphaDummy477),
        (nb078AlphaDummy478 g)), ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
        ((nb078AlphaDummy445), (nb078AlphaDummy447 g)), ((nb078AlphaDummy475),
        (nb078AlphaDummy476 g)), ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)), ((nb078AlphaDummy288),
        (nb078AlphaDummy291 g)), ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)), ((nb078AlphaDummy285),
        (nb078AlphaDummy286 g)), ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy453))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy471) from (by
          unfold
            nb078AlphaDummy471;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0484)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy472 g) from (by
          unfold
            nb078AlphaDummy472;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0485
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy469)
        from (by
          unfold
            nb078AlphaDummy469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0482)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy470 g) from (by
          unfold
            nb078AlphaDummy470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0483
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy471)
        from (by
          unfold
            nb078AlphaDummy471;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0484)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy472 g) from (by
          unfold
            nb078AlphaDummy472;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0485
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy469)
        from (by
          unfold
            nb078AlphaDummy469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0482)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy470 g) from (by
          unfold
            nb078AlphaDummy470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0483
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy473) from (by
          unfold
            nb078AlphaDummy473;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0488)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy474 g) from (by
          unfold
            nb078AlphaDummy474;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0489
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy469)
        from (by
          unfold
            nb078AlphaDummy469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0486)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy470 g) from (by
          unfold
            nb078AlphaDummy470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0487
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy461) ≠
        (nb078AlphaDummy473) from (by
          unfold
            nb078AlphaDummy473;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0488)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy474 g) from (by
          unfold
            nb078AlphaDummy474;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0489
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy469)
        from (by
          unfold
            nb078AlphaDummy469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0486)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy470 g) from (by
          unfold
            nb078AlphaDummy470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0487
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy453) ≠ (nb078AlphaDummy457) from
                                    (by
                                      unfold nb078AlphaDummy457;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0470)
                                              0)))) (show
                                    (nb078AlphaDummy455 g) ≠ (nb078AlphaDummy458 g) from
                                    (by
                                      unfold nb078AlphaDummy458;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0471 g)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb078AlphaDummy457), (nb078AlphaDummy458 g)),
                                  ((nb078AlphaDummy453), (nb078AlphaDummy455 g)),
                                  ((nb078AlphaDummy454), (nb078AlphaDummy456 g)),
                                  ((nb078AlphaDummy479), (nb078AlphaDummy480 g)),
                                  ((nb078AlphaDummy477), (nb078AlphaDummy478 g)),
                                  ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
                                  ((nb078AlphaDummy445), (nb078AlphaDummy447 g)),
                                  ((nb078AlphaDummy475), (nb078AlphaDummy476 g)),
                                  ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
                                  ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                  ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                  ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                  ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                  ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
                                  ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
                                  ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                  ((nb078AlphaDummy003), x)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078AlphaDummy453) ≠ (nb078AlphaDummy457) from (by
                                    unfold nb078AlphaDummy457;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0470) 0)))) (show
                                  (nb078AlphaDummy455 g) ≠ (nb078AlphaDummy458 g) from (by
                                    unfold nb078AlphaDummy458;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0471 g)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy453) ≠ (nb078AlphaDummy457) from
                                    (by
                                      unfold nb078AlphaDummy457;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0470)
                                              0)))) (show
                                    (nb078AlphaDummy455 g) ≠ (nb078AlphaDummy458 g) from
                                    (by
                                      unfold nb078AlphaDummy458;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0471 g)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb078AlphaDummy457), (nb078AlphaDummy458 g)),
                                  ((nb078AlphaDummy453), (nb078AlphaDummy455 g)),
                                  ((nb078AlphaDummy454), (nb078AlphaDummy456 g)),
                                  ((nb078AlphaDummy479), (nb078AlphaDummy480 g)),
                                  ((nb078AlphaDummy477), (nb078AlphaDummy478 g)),
                                  ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
                                  ((nb078AlphaDummy445), (nb078AlphaDummy447 g)),
                                  ((nb078AlphaDummy475), (nb078AlphaDummy476 g)),
                                  ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
                                  ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                  ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                  ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                  ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                  ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
                                  ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
                                  ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                  ((nb078AlphaDummy003), x)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0040`. -/
@[expose]
noncomputable def nb078SplitAlpha0040 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
        ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classEq (Class.cv (nb078AlphaDummy293))
          (synCop (Class.cv (nb078AlphaDummy287)) (Class.cv (nb078AlphaDummy288))))
        (Wff.neg (synWex (nb078AlphaDummy289) (synWa
              (synWbr (Class.cv (nb078AlphaDummy287))
                (synCcnv (Class.cv (nb078AlphaDummy001)))
                (Class.cv (nb078AlphaDummy289))) (synWbr (Class.cv (nb078AlphaDummy289))
                (Class.cv (nb078AlphaDummy001)) (Class.cv (nb078AlphaDummy288)))))))
      (Wff.imp (Wff.classEq (Class.cv (nb078AlphaDummy294 g))
          (synCop (Class.cv (nb078AlphaDummy290 g)) (Class.cv (nb078AlphaDummy291 g))))
        (Wff.neg (synWex (nb078AlphaDummy292 g) (synWa
              (synWbr (Class.cv (nb078AlphaDummy290 g)) (synCcnv (Class.cv g))
                (Class.cv (nb078AlphaDummy292 g)))
              (synWbr (Class.cv (nb078AlphaDummy292 g)) (Class.cv g)
                (Class.cv (nb078AlphaDummy291 g))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb078AlphaDummy288) ≠ (nb078AlphaDummy293) from (by
                unfold nb078AlphaDummy293;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0292) 0))))) (Ne.symm
            (show (nb078AlphaDummy291 g) ≠ (nb078AlphaDummy294 g) from (by
                unfold nb078AlphaDummy294;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0293 g) 0)))))
          (TAlphaVar.there (Ne.symm (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy293) from
                (by
                  unfold nb078AlphaDummy293;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0290) 0)))))
            (Ne.symm (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy294 g) from (by
                  unfold nb078AlphaDummy294;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0291 g) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0030 x y g)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy288) ≠ (nb078AlphaDummy296) from
                                    (by
                                      unfold nb078AlphaDummy296;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0322)
                                              1)))) (show
                                    (nb078AlphaDummy291 g) ≠ (nb078AlphaDummy298 g) from
                                    (by
                                      unfold nb078AlphaDummy298;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0324 g)
                                              1)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy288) ≠ (nb078AlphaDummy295) from (by
                                        unfold nb078AlphaDummy295;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0322)
                                                0)))) (show (nb078AlphaDummy291 g) ≠
                                        (nb078AlphaDummy297 g) from (by
                                        unfold nb078AlphaDummy297;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0324 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy288) ≠ (nb078AlphaDummy325) from
                                        (by
                                          unfold nb078AlphaDummy325;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0326)
                                                  0)))) (show (nb078AlphaDummy291 g) ≠
        (nb078AlphaDummy326 g) from (by
                                          unfold nb078AlphaDummy326;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0327 g) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy288) ≠
        (nb078AlphaDummy299) from (by
          unfold nb078AlphaDummy299;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0323) 0)))) (show (nb078AlphaDummy291 g) ≠
        (nb078AlphaDummy300 g) from (by
          unfold nb078AlphaDummy300;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0325 g) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb078AlphaDummy287))).fv ∪
                                      ((Class.cv (nb078AlphaDummy288))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy290 g))).fv ∪
                                      ((Class.cv (nb078AlphaDummy291 g))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078SplitAlpha0031 x y g)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy288) ≠ (nb078AlphaDummy296) from
                                    (by
                                      unfold nb078AlphaDummy296;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0322)
                                              1)))) (show
                                    (nb078AlphaDummy291 g) ≠ (nb078AlphaDummy298 g) from
                                    (by
                                      unfold nb078AlphaDummy298;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0324 g)
                                              1)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy288) ≠ (nb078AlphaDummy295) from (by
                                        unfold nb078AlphaDummy295;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0322)
                                                0)))) (show (nb078AlphaDummy291 g) ≠
                                        (nb078AlphaDummy297 g) from (by
                                        unfold nb078AlphaDummy297;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0324 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy288) ≠ (nb078AlphaDummy325) from
                                        (by
                                          unfold nb078AlphaDummy325;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0326)
                                                  0)))) (show (nb078AlphaDummy291 g) ≠
        (nb078AlphaDummy326 g) from (by
                                          unfold nb078AlphaDummy326;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0327 g) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy288) ≠
        (nb078AlphaDummy299) from (by
          unfold nb078AlphaDummy299;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0323) 0)))) (show (nb078AlphaDummy291 g) ≠
        (nb078AlphaDummy300 g) from (by
          unfold nb078AlphaDummy300;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0325 g) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb078AlphaDummy287))).fv ∪
                                      ((Class.cv (nb078AlphaDummy288))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy290 g))).fv ∪
                                      ((Class.cv (nb078AlphaDummy291 g))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078SplitAlpha0031 x y g)))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0032 x y g)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078AlphaDummy289) ≠
        (nb078AlphaDummy332) from (by
          unfold nb078AlphaDummy332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0360) 1)))) (show (nb078AlphaDummy292 g) ≠
        (nb078AlphaDummy334 g) from (by
          unfold nb078AlphaDummy334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0362 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy289) ≠ (nb078AlphaDummy331) from (by
          unfold nb078AlphaDummy331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0360) 0)))) (show (nb078AlphaDummy292 g) ≠
        (nb078AlphaDummy333 g) from (by
          unfold nb078AlphaDummy333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0362 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy289) ≠ (nb078AlphaDummy361) from (by
          unfold nb078AlphaDummy361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0364) 0)))) (show (nb078AlphaDummy292 g) ≠
        (nb078AlphaDummy362 g) from (by
          unfold nb078AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0365 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy289) ≠ (nb078AlphaDummy335) from (by
          unfold nb078AlphaDummy335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0361) 0)))) (show (nb078AlphaDummy292 g) ≠
        (nb078AlphaDummy336 g) from (by
          unfold nb078AlphaDummy336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0363 g) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078AlphaDummy287))).fv ∪ ((Class.cv (nb078AlphaDummy289))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy290 g))).fv ∪
        ((Class.cv (nb078AlphaDummy292 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078SplitAlpha0033 x y g)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy363), (nb078AlphaDummy364 g)), ((nb078AlphaDummy332),
        (nb078AlphaDummy334 g)), ((nb078AlphaDummy331), (nb078AlphaDummy333 g)),
        ((nb078AlphaDummy361), (nb078AlphaDummy362 g)), ((nb078AlphaDummy335),
        (nb078AlphaDummy336 g)), ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)), ((nb078AlphaDummy287),
        (nb078AlphaDummy290 g)), ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy285), (nb078AlphaDummy286 g)), ((nb078AlphaDummy283),
        (nb078AlphaDummy284 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078AlphaDummy289) ≠
        (nb078AlphaDummy332) from (by
          unfold nb078AlphaDummy332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0360) 1)))) (show (nb078AlphaDummy292 g) ≠
        (nb078AlphaDummy334 g) from (by
          unfold nb078AlphaDummy334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0362 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy289) ≠ (nb078AlphaDummy331) from (by
          unfold nb078AlphaDummy331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0360) 0)))) (show (nb078AlphaDummy292 g) ≠
        (nb078AlphaDummy333 g) from (by
          unfold nb078AlphaDummy333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0362 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy289) ≠ (nb078AlphaDummy361) from (by
          unfold nb078AlphaDummy361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0364) 0)))) (show (nb078AlphaDummy292 g) ≠
        (nb078AlphaDummy362 g) from (by
          unfold nb078AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0365 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy289) ≠ (nb078AlphaDummy335) from (by
          unfold nb078AlphaDummy335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0361) 0)))) (show (nb078AlphaDummy292 g) ≠
        (nb078AlphaDummy336 g) from (by
          unfold nb078AlphaDummy336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0363 g) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078AlphaDummy287))).fv ∪ ((Class.cv (nb078AlphaDummy289))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy290 g))).fv ∪
        ((Class.cv (nb078AlphaDummy292 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078SplitAlpha0033 x y g)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy363), (nb078AlphaDummy364 g)), ((nb078AlphaDummy332),
        (nb078AlphaDummy334 g)), ((nb078AlphaDummy331), (nb078AlphaDummy333 g)),
        ((nb078AlphaDummy361), (nb078AlphaDummy362 g)), ((nb078AlphaDummy335),
        (nb078AlphaDummy336 g)), ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)), ((nb078AlphaDummy287),
        (nb078AlphaDummy290 g)), ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy285), (nb078AlphaDummy286 g)), ((nb078AlphaDummy283),
        (nb078AlphaDummy284 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                            (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy371) from (by
                                unfold nb078AlphaDummy371;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0372) 0))))) (Ne.symm
                            (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy372 g) from (by
                                unfold nb078AlphaDummy372;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0373 g) 0)))))
                          (TAlphaVar.there (Ne.symm
                              (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy371) from (by
                                  unfold nb078AlphaDummy371;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0370) 0)))))
                            (Ne.symm (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy372 g)
                                from (by
                                  unfold nb078AlphaDummy372;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0371 g) 0)))))
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078SplitAlpha0034 x y g)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy374) from (by
          unfold nb078AlphaDummy374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0402)
                  1)))) (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy376 g) from (by
          unfold nb078AlphaDummy376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0404 g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy373)
        from (by
          unfold nb078AlphaDummy373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0402)
                  0)))) (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy375 g) from (by
          unfold nb078AlphaDummy375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0404 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy403)
        from (by
          unfold nb078AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0406)
                  0)))) (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy404 g) from (by
          unfold nb078AlphaDummy404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0407
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy377)
        from (by
          unfold nb078AlphaDummy377;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0403)
                  0)))) (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy378 g) from (by
          unfold nb078AlphaDummy378;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0405
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy367))).fv ∪
        ((Class.cv (nb078AlphaDummy368))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy369 g))).fv ∪ ((Class.cv (nb078AlphaDummy370 g))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0035 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy405), (nb078AlphaDummy406 g)), ((nb078AlphaDummy374),
        (nb078AlphaDummy376 g)), ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
        ((nb078AlphaDummy403), (nb078AlphaDummy404 g)), ((nb078AlphaDummy377),
        (nb078AlphaDummy378 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)), ((nb078AlphaDummy287),
        (nb078AlphaDummy290 g)), ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy285), (nb078AlphaDummy286 g)), ((nb078AlphaDummy283),
        (nb078AlphaDummy284 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy374) from (by
          unfold nb078AlphaDummy374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0402)
                  1)))) (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy376 g) from (by
          unfold nb078AlphaDummy376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0404 g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy373)
        from (by
          unfold nb078AlphaDummy373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0402)
                  0)))) (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy375 g) from (by
          unfold nb078AlphaDummy375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0404 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy403)
        from (by
          unfold nb078AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0406)
                  0)))) (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy404 g) from (by
          unfold nb078AlphaDummy404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0407
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy377)
        from (by
          unfold nb078AlphaDummy377;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0403)
                  0)))) (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy378 g) from (by
          unfold nb078AlphaDummy378;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0405
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy367))).fv ∪
        ((Class.cv (nb078AlphaDummy368))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy369 g))).fv ∪ ((Class.cv (nb078AlphaDummy370 g))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0035 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy405), (nb078AlphaDummy406 g)), ((nb078AlphaDummy374),
        (nb078AlphaDummy376 g)), ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
        ((nb078AlphaDummy403), (nb078AlphaDummy404 g)), ((nb078AlphaDummy377),
        (nb078AlphaDummy378 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)), ((nb078AlphaDummy287),
        (nb078AlphaDummy290 g)), ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy285), (nb078AlphaDummy286 g)), ((nb078AlphaDummy283),
        (nb078AlphaDummy284 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078SplitAlpha0036 x y g)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy410) from (by
          unfold nb078AlphaDummy410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0440)
                  1)))) (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy412 g) from (by
          unfold nb078AlphaDummy412;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0442 g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy409)
        from (by
          unfold nb078AlphaDummy409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0440)
                  0)))) (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy411 g) from (by
          unfold nb078AlphaDummy411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0442 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy439)
        from (by
          unfold nb078AlphaDummy439;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0444)
                  0)))) (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy440 g) from (by
          unfold nb078AlphaDummy440;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0445
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy413)
        from (by
          unfold nb078AlphaDummy413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0441)
                  0)))) (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy414 g) from (by
          unfold nb078AlphaDummy414;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0443
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy001))).fv) (by decide)) (freshVar_injective (((Class.cv g)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy368))).fv ∪
        ((Class.cv (nb078AlphaDummy367))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy370 g))).fv ∪ ((Class.cv (nb078AlphaDummy369 g))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0037 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy441), (nb078AlphaDummy442 g)), ((nb078AlphaDummy410),
        (nb078AlphaDummy412 g)), ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
        ((nb078AlphaDummy439), (nb078AlphaDummy440 g)), ((nb078AlphaDummy413),
        (nb078AlphaDummy414 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)), ((nb078AlphaDummy287),
        (nb078AlphaDummy290 g)), ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy285), (nb078AlphaDummy286 g)), ((nb078AlphaDummy283),
        (nb078AlphaDummy284 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy410) from (by
          unfold nb078AlphaDummy410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0440)
                  1)))) (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy412 g) from (by
          unfold nb078AlphaDummy412;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0442 g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy409)
        from (by
          unfold nb078AlphaDummy409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0440)
                  0)))) (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy411 g) from (by
          unfold nb078AlphaDummy411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0442 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy439)
        from (by
          unfold nb078AlphaDummy439;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0444)
                  0)))) (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy440 g) from (by
          unfold nb078AlphaDummy440;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0445
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy413)
        from (by
          unfold nb078AlphaDummy413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0441)
                  0)))) (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy414 g) from (by
          unfold nb078AlphaDummy414;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0443
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy001))).fv) (by decide)) (freshVar_injective (((Class.cv g)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy368))).fv ∪
        ((Class.cv (nb078AlphaDummy367))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy370 g))).fv ∪ ((Class.cv (nb078AlphaDummy369 g))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0037 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy441), (nb078AlphaDummy442 g)), ((nb078AlphaDummy410),
        (nb078AlphaDummy412 g)), ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
        ((nb078AlphaDummy439), (nb078AlphaDummy440 g)), ((nb078AlphaDummy413),
        (nb078AlphaDummy414 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)), ((nb078AlphaDummy287),
        (nb078AlphaDummy290 g)), ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy285), (nb078AlphaDummy286 g)), ((nb078AlphaDummy283),
        (nb078AlphaDummy284 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                          (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy368) from (by
                              unfold nb078AlphaDummy368;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0460) 1))))
                          (show g ≠ (nb078AlphaDummy370 g) from (by
                              unfold nb078AlphaDummy370;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0461 g) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy367) from (by
                                unfold nb078AlphaDummy367;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0460) 0))))
                            (show g ≠ (nb078AlphaDummy369 g) from (by
                                unfold nb078AlphaDummy369;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0461 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy371) from (by
                                  unfold nb078AlphaDummy371;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0458) 0))))
                              (show g ≠ (nb078AlphaDummy372 g) from (by
                                  unfold nb078AlphaDummy372;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0459 g) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy289) from (by
                                    unfold nb078AlphaDummy289;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0454) 2))))
                                (show g ≠ (nb078AlphaDummy292 g) from (by
                                    unfold nb078AlphaDummy292;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0456 g)
                                            2)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy288) from
                                    (by
                                      unfold nb078AlphaDummy288;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0454)
                                              1)))) (show g ≠ (nb078AlphaDummy291 g) from (by
                                      unfold nb078AlphaDummy291;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0456 g)
                                              1)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy001) ≠ (nb078AlphaDummy287) from (by
                                        unfold nb078AlphaDummy287;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0454)
                                                0)))) (show g ≠ (nb078AlphaDummy290 g) from
                                      (by
                                        unfold nb078AlphaDummy290;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0456 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy001) ≠ (nb078AlphaDummy293) from
                                        (by
                                          unfold nb078AlphaDummy293;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0455)
                                                  0)))) (show g ≠ (nb078AlphaDummy294 g) from
                                        (by
                                          unfold nb078AlphaDummy294;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0457 g) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy001) ≠
        (nb078AlphaDummy285) from (by
          unfold nb078AlphaDummy285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0452) 0)))) (show g ≠ (nb078AlphaDummy286 g) from (by
          unfold nb078AlphaDummy286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0453 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy001) ≠ (nb078AlphaDummy283) from (by
          unfold nb078AlphaDummy283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0450) 0)))) (show g ≠ (nb078AlphaDummy284 g) from (by
          unfold nb078AlphaDummy284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0451 g) 0)))) (TAlphaVar.here _ _ _)))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0038 x y g)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078AlphaDummy288) ≠
        (nb078AlphaDummy446) from (by
          unfold nb078AlphaDummy446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0490) 1)))) (show (nb078AlphaDummy291 g) ≠
        (nb078AlphaDummy448 g) from (by
          unfold nb078AlphaDummy448;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0492 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy288) ≠ (nb078AlphaDummy445) from (by
          unfold nb078AlphaDummy445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0490) 0)))) (show (nb078AlphaDummy291 g) ≠
        (nb078AlphaDummy447 g) from (by
          unfold nb078AlphaDummy447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0492 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy288) ≠ (nb078AlphaDummy475) from (by
          unfold nb078AlphaDummy475;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0494) 0)))) (show (nb078AlphaDummy291 g) ≠
        (nb078AlphaDummy476 g) from (by
          unfold nb078AlphaDummy476;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0495 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy288) ≠ (nb078AlphaDummy449) from (by
          unfold nb078AlphaDummy449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0491) 0)))) (show (nb078AlphaDummy291 g) ≠
        (nb078AlphaDummy450 g) from (by
          unfold nb078AlphaDummy450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0493 g) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy001))).fv ∪ ((synCcnv (Class.cv
        (nb078AlphaDummy001)))).fv) (by decide)) (freshVar_injective (((Class.cv g)).fv ∪
        ((synCcnv (Class.cv g))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078AlphaDummy289))).fv ∪ ((Class.cv (nb078AlphaDummy288))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy292 g))).fv ∪
        ((Class.cv (nb078AlphaDummy291 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078SplitAlpha0039 x y g)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy477), (nb078AlphaDummy478 g)), ((nb078AlphaDummy446),
        (nb078AlphaDummy448 g)), ((nb078AlphaDummy445), (nb078AlphaDummy447 g)),
        ((nb078AlphaDummy475), (nb078AlphaDummy476 g)), ((nb078AlphaDummy449),
        (nb078AlphaDummy450 g)), ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)), ((nb078AlphaDummy287),
        (nb078AlphaDummy290 g)), ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy285), (nb078AlphaDummy286 g)), ((nb078AlphaDummy283),
        (nb078AlphaDummy284 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078AlphaDummy288) ≠
        (nb078AlphaDummy446) from (by
          unfold nb078AlphaDummy446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0490) 1)))) (show (nb078AlphaDummy291 g) ≠
        (nb078AlphaDummy448 g) from (by
          unfold nb078AlphaDummy448;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0492 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy288) ≠ (nb078AlphaDummy445) from (by
          unfold nb078AlphaDummy445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0490) 0)))) (show (nb078AlphaDummy291 g) ≠
        (nb078AlphaDummy447 g) from (by
          unfold nb078AlphaDummy447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0492 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy288) ≠ (nb078AlphaDummy475) from (by
          unfold nb078AlphaDummy475;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0494) 0)))) (show (nb078AlphaDummy291 g) ≠
        (nb078AlphaDummy476 g) from (by
          unfold nb078AlphaDummy476;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0495 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy288) ≠ (nb078AlphaDummy449) from (by
          unfold nb078AlphaDummy449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0491) 0)))) (show (nb078AlphaDummy291 g) ≠
        (nb078AlphaDummy450 g) from (by
          unfold nb078AlphaDummy450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0493 g) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy001))).fv ∪ ((synCcnv (Class.cv
        (nb078AlphaDummy001)))).fv) (by decide)) (freshVar_injective (((Class.cv g)).fv ∪
        ((synCcnv (Class.cv g))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078AlphaDummy289))).fv ∪ ((Class.cv (nb078AlphaDummy288))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy292 g))).fv ∪
        ((Class.cv (nb078AlphaDummy291 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078SplitAlpha0039 x y g)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy477), (nb078AlphaDummy478 g)), ((nb078AlphaDummy446),
        (nb078AlphaDummy448 g)), ((nb078AlphaDummy445), (nb078AlphaDummy447 g)),
        ((nb078AlphaDummy475), (nb078AlphaDummy476 g)), ((nb078AlphaDummy449),
        (nb078AlphaDummy450 g)), ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)), ((nb078AlphaDummy287),
        (nb078AlphaDummy290 g)), ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy285), (nb078AlphaDummy286 g)), ((nb078AlphaDummy283),
        (nb078AlphaDummy284 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy289) from (by
                    unfold nb078AlphaDummy289;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0454) 2))))
                (show g ≠ (nb078AlphaDummy292 g) from (by
                    unfold nb078AlphaDummy292;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0456 g) 2))))
                (TAlphaVar.there (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy288) from
                    (by
                      unfold nb078AlphaDummy288;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0454) 1))))
                  (show g ≠ (nb078AlphaDummy291 g) from (by
                      unfold nb078AlphaDummy291;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0456 g) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy287) from
                      (by
                        unfold nb078AlphaDummy287;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0454) 0))))
                    (show g ≠ (nb078AlphaDummy290 g) from (by
                        unfold nb078AlphaDummy290;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0456 g) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy293) from (by
                          unfold nb078AlphaDummy293;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0455) 0))))
                      (show g ≠ (nb078AlphaDummy294 g) from (by
                          unfold nb078AlphaDummy294;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0457 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy285) from (by
                            unfold nb078AlphaDummy285;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0452) 0))))
                        (show g ≠ (nb078AlphaDummy286 g) from (by
                            unfold nb078AlphaDummy286;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0453 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy283) from (by
                              unfold nb078AlphaDummy283;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0450) 0))))
                          (show g ≠ (nb078AlphaDummy284 g) from (by
                              unfold nb078AlphaDummy284;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0451 g) 0))))
                          (TAlphaVar.here _ _ _)))))))))))))

theorem nb078_wpp_notmem_1216 : (nb078AlphaDummy285) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy285, fv_syn_cid] using (nb078_compact_fv_empty_0240)

theorem nb078_wpp_notmem_1217 (g : Var) : (nb078AlphaDummy286 g) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy286, fv_syn_cid] using (nb078_compact_fv_empty_0241 g)

theorem nb078_wpp_notmem_1218 : (nb078AlphaDummy283) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy283, fv_syn_cid] using (nb078_compact_fv_empty_0242)

theorem nb078_wpp_notmem_1219 (g : Var) : (nb078AlphaDummy284 g) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy284, fv_syn_cid] using (nb078_compact_fv_empty_0243 g)

theorem nb078_wpp_notmem_1220 : (nb078AlphaDummy001) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy001, fv_syn_cid] using (nb078_compact_fv_empty_0244)

theorem nb078_wpp_notmem_1221 (g : Var) : g ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb078_compact_fv_empty_0245 g)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
