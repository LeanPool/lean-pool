/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block038

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part118`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0093`. -/
@[expose]
noncomputable def nb078SplitAlpha0093 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy443), (nb078AlphaDummy444 g)),
        ((nb078AlphaDummy441), (nb078AlphaDummy442 g)),
        ((nb078AlphaDummy410), (nb078AlphaDummy412 g)),
        ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
        ((nb078AlphaDummy439), (nb078AlphaDummy440 g)),
        ((nb078AlphaDummy413), (nb078AlphaDummy414 g)),
        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
        ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
        ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy443))
          (synCphi (Class.cv (nb078AlphaDummy410)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy443))
            (synCphi (Class.cv (nb078AlphaDummy410))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy444 g))
          (synCphi (Class.cv (nb078AlphaDummy412 g)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy444 g))
            (synCphi (Class.cv (nb078AlphaDummy412 g)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy410) ≠ (nb078AlphaDummy417) from
                    (by
                      unfold nb078AlphaDummy417;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0418) 0))))
                  (show (nb078AlphaDummy412 g) ≠ (nb078AlphaDummy419 g) from (by
                      unfold nb078AlphaDummy419;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0419 g) 0))))
                  (TAlphaVar.there (show (nb078AlphaDummy410) ≠ (nb078AlphaDummy418) from
                      (by
                        unfold nb078AlphaDummy418;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0418) 1))))
                    (show (nb078AlphaDummy412 g) ≠ (nb078AlphaDummy420 g) from (by
                        unfold nb078AlphaDummy420;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0419 g) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy410) ≠ (nb078AlphaDummy443) from (by
                          unfold nb078AlphaDummy443;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0448) 0))))
                      (show (nb078AlphaDummy412 g) ≠ (nb078AlphaDummy444 g) from (by
                          unfold nb078AlphaDummy444;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0449 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy410) ≠ (nb078AlphaDummy441) from (by
                            unfold nb078AlphaDummy441;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0446) 0))))
                        (show (nb078AlphaDummy412 g) ≠ (nb078AlphaDummy442 g) from (by
                            unfold nb078AlphaDummy442;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0447 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy410))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy412 g))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy417) ≠ (nb078AlphaDummy424) from (by
                                        unfold nb078AlphaDummy424;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0422)
                                                1)))) (show (nb078AlphaDummy419 g) ≠
                                        (nb078AlphaDummy427 g) from (by
                                        unfold nb078AlphaDummy427;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0423 g)
                                                1)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy417) ≠ (nb078AlphaDummy423) from
                                        (by
                                          unfold nb078AlphaDummy423;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0422)
                                                  0)))) (show (nb078AlphaDummy419 g) ≠
        (nb078AlphaDummy426 g) from (by
                                          unfold nb078AlphaDummy426;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0423 g) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy417) ≠
        (nb078AlphaDummy421) from (by
          unfold nb078AlphaDummy421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0420) 0)))) (show (nb078AlphaDummy419 g) ≠
        (nb078AlphaDummy422 g) from (by
          unfold nb078AlphaDummy422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0421 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb078AlphaDummy425),
        (nb078AlphaDummy428 g)), ((nb078AlphaDummy424), (nb078AlphaDummy427 g)),
                                        ((nb078AlphaDummy423), (nb078AlphaDummy426 g)),
                                        ((nb078AlphaDummy421), (nb078AlphaDummy422 g)),
                                        ((nb078AlphaDummy417), (nb078AlphaDummy419 g)),
                                        ((nb078AlphaDummy418), (nb078AlphaDummy420 g)),
                                        ((nb078AlphaDummy443), (nb078AlphaDummy444 g)),
                                        ((nb078AlphaDummy441), (nb078AlphaDummy442 g)),
                                        ((nb078AlphaDummy410), (nb078AlphaDummy412 g)),
                                        ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
                                        ((nb078AlphaDummy439), (nb078AlphaDummy440 g)),
                                        ((nb078AlphaDummy413), (nb078AlphaDummy414 g)),
                                        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                                        ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                                        ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                                        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                                        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                        ((nb078AlphaDummy001), g),
                                        ((nb078AlphaDummy004), y),
                                        ((nb078AlphaDummy003), x)]
                                      (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy424) ≠
        (nb078AlphaDummy431) from (by
          unfold
            nb078AlphaDummy431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0426)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy432 g) from (by
          unfold
            nb078AlphaDummy432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0427
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy429)
        from (by
          unfold
            nb078AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0424)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy430 g) from (by
          unfold
            nb078AlphaDummy430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0425
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy431)
        from (by
          unfold
            nb078AlphaDummy431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0430)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy432 g) from (by
          unfold
            nb078AlphaDummy432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0431
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy429)
        from (by
          unfold
            nb078AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0428)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy430 g) from (by
          unfold
            nb078AlphaDummy430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0429
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy431) from (by
          unfold
            nb078AlphaDummy431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0426)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy432 g) from (by
          unfold
            nb078AlphaDummy432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0427
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy429)
        from (by
          unfold
            nb078AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0424)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy430 g) from (by
          unfold
            nb078AlphaDummy430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0425
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy431)
        from (by
          unfold
            nb078AlphaDummy431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0430)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy432 g) from (by
          unfold
            nb078AlphaDummy432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0431
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy429)
        from (by
          unfold
            nb078AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0428)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy430 g) from (by
          unfold
            nb078AlphaDummy430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0429
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb078AlphaDummy425), (nb078AlphaDummy428 g)),
        ((nb078AlphaDummy424), (nb078AlphaDummy427 g)), ((nb078AlphaDummy423),
        (nb078AlphaDummy426 g)), ((nb078AlphaDummy421), (nb078AlphaDummy422 g)),
        ((nb078AlphaDummy417), (nb078AlphaDummy419 g)), ((nb078AlphaDummy418),
        (nb078AlphaDummy420 g)), ((nb078AlphaDummy443), (nb078AlphaDummy444 g)),
        ((nb078AlphaDummy441), (nb078AlphaDummy442 g)), ((nb078AlphaDummy410),
        (nb078AlphaDummy412 g)), ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
        ((nb078AlphaDummy439), (nb078AlphaDummy440 g)), ((nb078AlphaDummy413),
        (nb078AlphaDummy414 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
        ((nb078AlphaDummy649), (nb078AlphaDummy651 g)), ((nb078AlphaDummy653),
        (nb078AlphaDummy654 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy424) ≠
        (nb078AlphaDummy435) from (by
          unfold
            nb078AlphaDummy435;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0434)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy436 g) from (by
          unfold
            nb078AlphaDummy436;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0435
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy433)
        from (by
          unfold
            nb078AlphaDummy433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0432)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy434 g) from (by
          unfold
            nb078AlphaDummy434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0433
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy435)
        from (by
          unfold
            nb078AlphaDummy435;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0434)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy436 g) from (by
          unfold
            nb078AlphaDummy436;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0435
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy433)
        from (by
          unfold
            nb078AlphaDummy433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0432)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy434 g) from (by
          unfold
            nb078AlphaDummy434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0433
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy437) from (by
          unfold
            nb078AlphaDummy437;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0438)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy438 g) from (by
          unfold
            nb078AlphaDummy438;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0439
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy433)
        from (by
          unfold
            nb078AlphaDummy433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0436)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy434 g) from (by
          unfold
            nb078AlphaDummy434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0437
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy425) ≠
        (nb078AlphaDummy437) from (by
          unfold
            nb078AlphaDummy437;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0438)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy438 g) from (by
          unfold
            nb078AlphaDummy438;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0439
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy433)
        from (by
          unfold
            nb078AlphaDummy433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0436)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy434 g) from (by
          unfold
            nb078AlphaDummy434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0437
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from (by
                                unfold nb078AlphaDummy421;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0420) 0))))
                            (show (nb078AlphaDummy419 g) ≠ (nb078AlphaDummy422 g) from (by
                                unfold nb078AlphaDummy422;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0421 g) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy421), (nb078AlphaDummy422 g)),
                            ((nb078AlphaDummy417), (nb078AlphaDummy419 g)),
                            ((nb078AlphaDummy418), (nb078AlphaDummy420 g)),
                            ((nb078AlphaDummy443), (nb078AlphaDummy444 g)),
                            ((nb078AlphaDummy441), (nb078AlphaDummy442 g)),
                            ((nb078AlphaDummy410), (nb078AlphaDummy412 g)),
                            ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
                            ((nb078AlphaDummy439), (nb078AlphaDummy440 g)),
                            ((nb078AlphaDummy413), (nb078AlphaDummy414 g)),
                            ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                            ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                            ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                            ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                            ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                            ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                            ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                            ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                            ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                            ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                            ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from (by
                              unfold nb078AlphaDummy421;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0420) 0))))
                          (show (nb078AlphaDummy419 g) ≠ (nb078AlphaDummy422 g) from (by
                              unfold nb078AlphaDummy422;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0421 g) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from (by
                                unfold nb078AlphaDummy421;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0420) 0))))
                            (show (nb078AlphaDummy419 g) ≠ (nb078AlphaDummy422 g) from (by
                                unfold nb078AlphaDummy422;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0421 g) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy421), (nb078AlphaDummy422 g)),
                            ((nb078AlphaDummy417), (nb078AlphaDummy419 g)),
                            ((nb078AlphaDummy418), (nb078AlphaDummy420 g)),
                            ((nb078AlphaDummy443), (nb078AlphaDummy444 g)),
                            ((nb078AlphaDummy441), (nb078AlphaDummy442 g)),
                            ((nb078AlphaDummy410), (nb078AlphaDummy412 g)),
                            ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
                            ((nb078AlphaDummy439), (nb078AlphaDummy440 g)),
                            ((nb078AlphaDummy413), (nb078AlphaDummy414 g)),
                            ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                            ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                            ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                            ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                            ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                            ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                            ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                            ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                            ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                            ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                            ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078AlphaDummy410) ≠ (nb078AlphaDummy417) from (by
                        unfold nb078AlphaDummy417;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0418) 0))))
                    (show (nb078AlphaDummy412 g) ≠ (nb078AlphaDummy419 g) from (by
                        unfold nb078AlphaDummy419;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0419 g) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy410) ≠ (nb078AlphaDummy418) from (by
                          unfold nb078AlphaDummy418;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0418) 1))))
                      (show (nb078AlphaDummy412 g) ≠ (nb078AlphaDummy420 g) from (by
                          unfold nb078AlphaDummy420;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0419 g) 1))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy410) ≠ (nb078AlphaDummy443) from (by
                            unfold nb078AlphaDummy443;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0448) 0))))
                        (show (nb078AlphaDummy412 g) ≠ (nb078AlphaDummy444 g) from (by
                            unfold nb078AlphaDummy444;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0449 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy410) ≠ (nb078AlphaDummy441) from (by
                              unfold nb078AlphaDummy441;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0446) 0))))
                          (show (nb078AlphaDummy412 g) ≠ (nb078AlphaDummy442 g) from (by
                              unfold nb078AlphaDummy442;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0447 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy410))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy412 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078AlphaDummy417) ≠ (nb078AlphaDummy424) from
                                        (by
                                          unfold nb078AlphaDummy424;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0422)
                                                  1)))) (show (nb078AlphaDummy419 g) ≠
        (nb078AlphaDummy427 g) from (by
                                          unfold nb078AlphaDummy427;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0423 g) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy417) ≠
        (nb078AlphaDummy423) from (by
          unfold nb078AlphaDummy423;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0422) 0)))) (show (nb078AlphaDummy419 g) ≠
        (nb078AlphaDummy426 g) from (by
          unfold nb078AlphaDummy426;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0423 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from (by
          unfold nb078AlphaDummy421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0420) 0)))) (show (nb078AlphaDummy419 g) ≠
        (nb078AlphaDummy422 g) from (by
          unfold nb078AlphaDummy422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0421 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb078AlphaDummy425),
        (nb078AlphaDummy428 g)), ((nb078AlphaDummy424), (nb078AlphaDummy427 g)),
        ((nb078AlphaDummy423), (nb078AlphaDummy426 g)), ((nb078AlphaDummy421),
        (nb078AlphaDummy422 g)), ((nb078AlphaDummy417), (nb078AlphaDummy419 g)),
        ((nb078AlphaDummy418), (nb078AlphaDummy420 g)), ((nb078AlphaDummy443),
        (nb078AlphaDummy444 g)), ((nb078AlphaDummy441), (nb078AlphaDummy442 g)),
        ((nb078AlphaDummy410), (nb078AlphaDummy412 g)), ((nb078AlphaDummy409),
        (nb078AlphaDummy411 g)), ((nb078AlphaDummy439), (nb078AlphaDummy440 g)),
        ((nb078AlphaDummy413), (nb078AlphaDummy414 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy650),
        (nb078AlphaDummy652 g)), ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy424) ≠
        (nb078AlphaDummy431) from (by
          unfold
            nb078AlphaDummy431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0426)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy432 g) from (by
          unfold
            nb078AlphaDummy432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0427
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy429)
        from (by
          unfold
            nb078AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0424)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy430 g) from (by
          unfold
            nb078AlphaDummy430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0425
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy431)
        from (by
          unfold
            nb078AlphaDummy431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0430)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy432 g) from (by
          unfold
            nb078AlphaDummy432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0431
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy429)
        from (by
          unfold
            nb078AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0428)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy430 g) from (by
          unfold
            nb078AlphaDummy430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0429
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy431) from (by
          unfold
            nb078AlphaDummy431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0426)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy432 g) from (by
          unfold
            nb078AlphaDummy432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0427
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy429)
        from (by
          unfold
            nb078AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0424)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy430 g) from (by
          unfold
            nb078AlphaDummy430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0425
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy431)
        from (by
          unfold
            nb078AlphaDummy431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0430)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy432 g) from (by
          unfold
            nb078AlphaDummy432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0431
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy429)
        from (by
          unfold
            nb078AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0428)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy430 g) from (by
          unfold
            nb078AlphaDummy430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0429
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy425), (nb078AlphaDummy428 g)), ((nb078AlphaDummy424),
        (nb078AlphaDummy427 g)), ((nb078AlphaDummy423), (nb078AlphaDummy426 g)),
        ((nb078AlphaDummy421), (nb078AlphaDummy422 g)), ((nb078AlphaDummy417),
        (nb078AlphaDummy419 g)), ((nb078AlphaDummy418), (nb078AlphaDummy420 g)),
        ((nb078AlphaDummy443), (nb078AlphaDummy444 g)), ((nb078AlphaDummy441),
        (nb078AlphaDummy442 g)), ((nb078AlphaDummy410), (nb078AlphaDummy412 g)),
        ((nb078AlphaDummy409), (nb078AlphaDummy411 g)), ((nb078AlphaDummy439),
        (nb078AlphaDummy440 g)), ((nb078AlphaDummy413), (nb078AlphaDummy414 g)),
        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)), ((nb078AlphaDummy367),
        (nb078AlphaDummy369 g)), ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
        ((nb078AlphaDummy650), (nb078AlphaDummy652 g)), ((nb078AlphaDummy649),
        (nb078AlphaDummy651 g)), ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)), ((nb078AlphaDummy570),
        (nb078AlphaDummy573 g)), ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy417))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy417))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy424) ≠
        (nb078AlphaDummy435) from (by
          unfold
            nb078AlphaDummy435;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0434)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy436 g) from (by
          unfold
            nb078AlphaDummy436;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0435
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy433)
        from (by
          unfold
            nb078AlphaDummy433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0432)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy434 g) from (by
          unfold
            nb078AlphaDummy434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0433
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy435)
        from (by
          unfold
            nb078AlphaDummy435;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0434)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy436 g) from (by
          unfold
            nb078AlphaDummy436;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0435
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy433)
        from (by
          unfold
            nb078AlphaDummy433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0432)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy434 g) from (by
          unfold
            nb078AlphaDummy434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0433
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy437) from (by
          unfold
            nb078AlphaDummy437;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0438)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy438 g) from (by
          unfold
            nb078AlphaDummy438;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0439
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy433)
        from (by
          unfold
            nb078AlphaDummy433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0436)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy434 g) from (by
          unfold
            nb078AlphaDummy434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0437
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy425) ≠
        (nb078AlphaDummy437) from (by
          unfold
            nb078AlphaDummy437;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0438)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy438 g) from (by
          unfold
            nb078AlphaDummy438;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0439
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy433)
        from (by
          unfold
            nb078AlphaDummy433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0436)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy434 g) from (by
          unfold
            nb078AlphaDummy434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0437
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from (by
                                  unfold nb078AlphaDummy421;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0420) 0))))
                              (show (nb078AlphaDummy419 g) ≠ (nb078AlphaDummy422 g) from
                                (by
                                  unfold nb078AlphaDummy422;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0421 g) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy421), (nb078AlphaDummy422 g)),
                              ((nb078AlphaDummy417), (nb078AlphaDummy419 g)),
                              ((nb078AlphaDummy418), (nb078AlphaDummy420 g)),
                              ((nb078AlphaDummy443), (nb078AlphaDummy444 g)),
                              ((nb078AlphaDummy441), (nb078AlphaDummy442 g)),
                              ((nb078AlphaDummy410), (nb078AlphaDummy412 g)),
                              ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
                              ((nb078AlphaDummy439), (nb078AlphaDummy440 g)),
                              ((nb078AlphaDummy413), (nb078AlphaDummy414 g)),
                              ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                              ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                              ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                              ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                              ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                              ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                              ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                              ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                              ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                              ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                              ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from (by
                                unfold nb078AlphaDummy421;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0420) 0))))
                            (show (nb078AlphaDummy419 g) ≠ (nb078AlphaDummy422 g) from (by
                                unfold nb078AlphaDummy422;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0421 g) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from (by
                                  unfold nb078AlphaDummy421;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0420) 0))))
                              (show (nb078AlphaDummy419 g) ≠ (nb078AlphaDummy422 g) from
                                (by
                                  unfold nb078AlphaDummy422;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0421 g) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy421), (nb078AlphaDummy422 g)),
                              ((nb078AlphaDummy417), (nb078AlphaDummy419 g)),
                              ((nb078AlphaDummy418), (nb078AlphaDummy420 g)),
                              ((nb078AlphaDummy443), (nb078AlphaDummy444 g)),
                              ((nb078AlphaDummy441), (nb078AlphaDummy442 g)),
                              ((nb078AlphaDummy410), (nb078AlphaDummy412 g)),
                              ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
                              ((nb078AlphaDummy439), (nb078AlphaDummy440 g)),
                              ((nb078AlphaDummy413), (nb078AlphaDummy414 g)),
                              ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                              ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                              ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                              ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                              ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                              ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                              ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                              ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                              ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                              ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                              ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0094`. -/
@[expose]
noncomputable def nb078SplitAlpha0094 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.classMem
        (synCop (Class.cv (nb078AlphaDummy569)) (Class.cv (nb078AlphaDummy571)))
        (synCcnv (synCcnv (Class.cv (nb078AlphaDummy001)))))
      (Wff.classMem (synCop (Class.cv (nb078AlphaDummy572 g))
          (Class.cv (nb078AlphaDummy574 g))) (synCcnv (synCcnv (Class.cv g)))) :=
  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0084 x y g)))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078AlphaDummy571) ≠ (nb078AlphaDummy614) from (by
                                    unfold nb078AlphaDummy614;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0658) 1)))) (show
                                  (nb078AlphaDummy574 g) ≠ (nb078AlphaDummy616 g) from (by
                                    unfold nb078AlphaDummy616;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0660 g)
                                            1)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy571) ≠ (nb078AlphaDummy613) from
                                    (by
                                      unfold nb078AlphaDummy613;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0658)
                                              0)))) (show
                                    (nb078AlphaDummy574 g) ≠ (nb078AlphaDummy615 g) from
                                    (by
                                      unfold nb078AlphaDummy615;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0660 g)
                                              0)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy571) ≠ (nb078AlphaDummy643) from (by
                                        unfold nb078AlphaDummy643;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0662)
                                                0)))) (show (nb078AlphaDummy574 g) ≠
                                        (nb078AlphaDummy644 g) from (by
                                        unfold nb078AlphaDummy644;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0663 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy571) ≠ (nb078AlphaDummy617) from
                                        (by
                                          unfold nb078AlphaDummy617;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0659)
                                                  0)))) (show (nb078AlphaDummy574 g) ≠
        (nb078AlphaDummy618 g) from (by
                                          unfold nb078AlphaDummy618;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0661 g) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb078AlphaDummy569))).fv ∪
                                    ((Class.cv (nb078AlphaDummy571))).fv) (by decide))
                                (freshVar_injective (((Class.cv (nb078AlphaDummy572 g))).fv ∪
                                    ((Class.cv (nb078AlphaDummy574 g))).fv) (by decide))
                                (TAlphaVar.here _ _ _)))
                            (TAlphaClass.cab (nb078SplitAlpha0085 x y g)))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078AlphaDummy571) ≠ (nb078AlphaDummy614) from (by
                                    unfold nb078AlphaDummy614;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0658) 1)))) (show
                                  (nb078AlphaDummy574 g) ≠ (nb078AlphaDummy616 g) from (by
                                    unfold nb078AlphaDummy616;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0660 g)
                                            1)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy571) ≠ (nb078AlphaDummy613) from
                                    (by
                                      unfold nb078AlphaDummy613;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0658)
                                              0)))) (show
                                    (nb078AlphaDummy574 g) ≠ (nb078AlphaDummy615 g) from
                                    (by
                                      unfold nb078AlphaDummy615;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0660 g)
                                              0)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy571) ≠ (nb078AlphaDummy643) from (by
                                        unfold nb078AlphaDummy643;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0662)
                                                0)))) (show (nb078AlphaDummy574 g) ≠
                                        (nb078AlphaDummy644 g) from (by
                                        unfold nb078AlphaDummy644;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0663 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy571) ≠ (nb078AlphaDummy617) from
                                        (by
                                          unfold nb078AlphaDummy617;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0659)
                                                  0)))) (show (nb078AlphaDummy574 g) ≠
        (nb078AlphaDummy618 g) from (by
                                          unfold nb078AlphaDummy618;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0661 g) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb078AlphaDummy569))).fv ∪
                                    ((Class.cv (nb078AlphaDummy571))).fv) (by decide))
                                (freshVar_injective (((Class.cv (nb078AlphaDummy572 g))).fv ∪
                                    ((Class.cv (nb078AlphaDummy574 g))).fv) (by decide))
                                (TAlphaVar.here _ _ _)))
                            (TAlphaClass.cab (nb078SplitAlpha0085 x y g))))))))))))))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                    (show (nb078AlphaDummy650) ≠ (nb078AlphaDummy653) from (by
                        unfold nb078AlphaDummy653;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0670) 0)))))
                  (Ne.symm (show (nb078AlphaDummy652 g) ≠ (nb078AlphaDummy654 g) from (by
                        unfold nb078AlphaDummy654;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0671 g) 0)))))
                  (TAlphaVar.there (Ne.symm
                      (show (nb078AlphaDummy649) ≠ (nb078AlphaDummy653) from (by
                          unfold nb078AlphaDummy653;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0668) 0))))) (Ne.symm
                      (show (nb078AlphaDummy651 g) ≠ (nb078AlphaDummy654 g) from (by
                          unfold nb078AlphaDummy654;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0669 g) 0)))))
                    (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0086 x y g)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy650) ≠
        (nb078AlphaDummy656) from (by
          unfold nb078AlphaDummy656;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0700) 1)))) (show (nb078AlphaDummy652 g) ≠
        (nb078AlphaDummy658 g) from (by
          unfold nb078AlphaDummy658;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0702 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy650) ≠ (nb078AlphaDummy655) from (by
          unfold nb078AlphaDummy655;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0700) 0)))) (show (nb078AlphaDummy652 g) ≠
        (nb078AlphaDummy657 g) from (by
          unfold nb078AlphaDummy657;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0702 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy650) ≠ (nb078AlphaDummy685) from (by
          unfold nb078AlphaDummy685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0704) 0)))) (show (nb078AlphaDummy652 g) ≠
        (nb078AlphaDummy686 g) from (by
          unfold nb078AlphaDummy686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0705 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy650) ≠ (nb078AlphaDummy659) from (by
          unfold nb078AlphaDummy659;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0701) 0)))) (show (nb078AlphaDummy652 g) ≠
        (nb078AlphaDummy660 g) from (by
          unfold nb078AlphaDummy660;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0703 g)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy649))).fv ∪ ((Class.cv (nb078AlphaDummy650))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy651 g))).fv ∪
        ((Class.cv (nb078AlphaDummy652 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0087 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy687), (nb078AlphaDummy688 g)), ((nb078AlphaDummy656),
        (nb078AlphaDummy658 g)), ((nb078AlphaDummy655), (nb078AlphaDummy657 g)),
        ((nb078AlphaDummy685), (nb078AlphaDummy686 g)), ((nb078AlphaDummy659),
        (nb078AlphaDummy660 g)), ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
        ((nb078AlphaDummy649), (nb078AlphaDummy651 g)), ((nb078AlphaDummy653),
        (nb078AlphaDummy654 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy650) ≠
        (nb078AlphaDummy656) from (by
          unfold nb078AlphaDummy656;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0700) 1)))) (show (nb078AlphaDummy652 g) ≠
        (nb078AlphaDummy658 g) from (by
          unfold nb078AlphaDummy658;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0702 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy650) ≠ (nb078AlphaDummy655) from (by
          unfold nb078AlphaDummy655;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0700) 0)))) (show (nb078AlphaDummy652 g) ≠
        (nb078AlphaDummy657 g) from (by
          unfold nb078AlphaDummy657;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0702 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy650) ≠ (nb078AlphaDummy685) from (by
          unfold nb078AlphaDummy685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0704) 0)))) (show (nb078AlphaDummy652 g) ≠
        (nb078AlphaDummy686 g) from (by
          unfold nb078AlphaDummy686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0705 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy650) ≠ (nb078AlphaDummy659) from (by
          unfold nb078AlphaDummy659;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0701) 0)))) (show (nb078AlphaDummy652 g) ≠
        (nb078AlphaDummy660 g) from (by
          unfold nb078AlphaDummy660;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0703 g)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy649))).fv ∪ ((Class.cv (nb078AlphaDummy650))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy651 g))).fv ∪
        ((Class.cv (nb078AlphaDummy652 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0087 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy687), (nb078AlphaDummy688 g)), ((nb078AlphaDummy656),
        (nb078AlphaDummy658 g)), ((nb078AlphaDummy655), (nb078AlphaDummy657 g)),
        ((nb078AlphaDummy685), (nb078AlphaDummy686 g)), ((nb078AlphaDummy659),
        (nb078AlphaDummy660 g)), ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
        ((nb078AlphaDummy649), (nb078AlphaDummy651 g)), ((nb078AlphaDummy653),
        (nb078AlphaDummy654 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0088 x y g)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy649) ≠
        (nb078AlphaDummy692) from (by
          unfold nb078AlphaDummy692;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0738) 1)))) (show (nb078AlphaDummy651 g) ≠
        (nb078AlphaDummy694 g) from (by
          unfold nb078AlphaDummy694;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0740 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy649) ≠ (nb078AlphaDummy691) from (by
          unfold nb078AlphaDummy691;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0738) 0)))) (show (nb078AlphaDummy651 g) ≠
        (nb078AlphaDummy693 g) from (by
          unfold nb078AlphaDummy693;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0740 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy649) ≠ (nb078AlphaDummy721) from (by
          unfold nb078AlphaDummy721;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0742) 0)))) (show (nb078AlphaDummy651 g) ≠
        (nb078AlphaDummy722 g) from (by
          unfold nb078AlphaDummy722;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0743 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy649) ≠ (nb078AlphaDummy695) from (by
          unfold nb078AlphaDummy695;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0739) 0)))) (show (nb078AlphaDummy651 g) ≠
        (nb078AlphaDummy696 g) from (by
          unfold nb078AlphaDummy696;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0741 g)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (Class.cv
        (nb078AlphaDummy001)))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv g))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078AlphaDummy650))).fv ∪
        ((Class.cv (nb078AlphaDummy649))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy652 g))).fv ∪ ((Class.cv (nb078AlphaDummy651 g))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0089 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy723), (nb078AlphaDummy724 g)), ((nb078AlphaDummy692),
        (nb078AlphaDummy694 g)), ((nb078AlphaDummy691), (nb078AlphaDummy693 g)),
        ((nb078AlphaDummy721), (nb078AlphaDummy722 g)), ((nb078AlphaDummy695),
        (nb078AlphaDummy696 g)), ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
        ((nb078AlphaDummy649), (nb078AlphaDummy651 g)), ((nb078AlphaDummy653),
        (nb078AlphaDummy654 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy649) ≠
        (nb078AlphaDummy692) from (by
          unfold nb078AlphaDummy692;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0738) 1)))) (show (nb078AlphaDummy651 g) ≠
        (nb078AlphaDummy694 g) from (by
          unfold nb078AlphaDummy694;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0740 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy649) ≠ (nb078AlphaDummy691) from (by
          unfold nb078AlphaDummy691;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0738) 0)))) (show (nb078AlphaDummy651 g) ≠
        (nb078AlphaDummy693 g) from (by
          unfold nb078AlphaDummy693;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0740 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy649) ≠ (nb078AlphaDummy721) from (by
          unfold nb078AlphaDummy721;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0742) 0)))) (show (nb078AlphaDummy651 g) ≠
        (nb078AlphaDummy722 g) from (by
          unfold nb078AlphaDummy722;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0743 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy649) ≠ (nb078AlphaDummy695) from (by
          unfold nb078AlphaDummy695;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0739) 0)))) (show (nb078AlphaDummy651 g) ≠
        (nb078AlphaDummy696 g) from (by
          unfold nb078AlphaDummy696;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0741 g)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (Class.cv
        (nb078AlphaDummy001)))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv g))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078AlphaDummy650))).fv ∪
        ((Class.cv (nb078AlphaDummy649))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy652 g))).fv ∪ ((Class.cv (nb078AlphaDummy651 g))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0089 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy723), (nb078AlphaDummy724 g)), ((nb078AlphaDummy692),
        (nb078AlphaDummy694 g)), ((nb078AlphaDummy691), (nb078AlphaDummy693 g)),
        ((nb078AlphaDummy721), (nb078AlphaDummy722 g)), ((nb078AlphaDummy695),
        (nb078AlphaDummy696 g)), ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
        ((nb078AlphaDummy649), (nb078AlphaDummy651 g)), ((nb078AlphaDummy653),
        (nb078AlphaDummy654 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                              (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy371) from (by
                                  unfold nb078AlphaDummy371;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0372) 0)))))
                            (Ne.symm (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy372 g)
                                from (by
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
                              (Ne.symm (show
                                  (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy372 g) from (by
                                    unfold nb078AlphaDummy372;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0371 g)
                                            0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb078SplitAlpha0090 x y g)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy368) ≠ (nb078AlphaDummy374) from (by
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
                  (nb078_support_mem_0404
                    g)
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
          unfold
            nb078AlphaDummy377;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0403)
                  0)))) (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy378 g) from (by
          unfold
            nb078AlphaDummy378;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0091 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy405), (nb078AlphaDummy406 g)), ((nb078AlphaDummy374),
        (nb078AlphaDummy376 g)), ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
        ((nb078AlphaDummy403), (nb078AlphaDummy404 g)), ((nb078AlphaDummy377),
        (nb078AlphaDummy378 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
        ((nb078AlphaDummy649), (nb078AlphaDummy651 g)), ((nb078AlphaDummy653),
        (nb078AlphaDummy654 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
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
                  (nb078_support_mem_0404
                    g)
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
          unfold
            nb078AlphaDummy377;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0403)
                  0)))) (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy378 g) from (by
          unfold
            nb078AlphaDummy378;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0091 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy405), (nb078AlphaDummy406 g)), ((nb078AlphaDummy374),
        (nb078AlphaDummy376 g)), ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
        ((nb078AlphaDummy403), (nb078AlphaDummy404 g)), ((nb078AlphaDummy377),
        (nb078AlphaDummy378 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
        ((nb078AlphaDummy649), (nb078AlphaDummy651 g)), ((nb078AlphaDummy653),
        (nb078AlphaDummy654 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb078SplitAlpha0092 x y g)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy367) ≠ (nb078AlphaDummy410) from (by
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
                  (nb078_support_mem_0442
                    g)
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
          unfold
            nb078AlphaDummy413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0441)
                  0)))) (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy414 g) from (by
          unfold
            nb078AlphaDummy414;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0093 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy441), (nb078AlphaDummy442 g)), ((nb078AlphaDummy410),
        (nb078AlphaDummy412 g)), ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
        ((nb078AlphaDummy439), (nb078AlphaDummy440 g)), ((nb078AlphaDummy413),
        (nb078AlphaDummy414 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
        ((nb078AlphaDummy649), (nb078AlphaDummy651 g)), ((nb078AlphaDummy653),
        (nb078AlphaDummy654 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
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
                  (nb078_support_mem_0442
                    g)
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
          unfold
            nb078AlphaDummy413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0441)
                  0)))) (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy414 g) from (by
          unfold
            nb078AlphaDummy414;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0093 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy441), (nb078AlphaDummy442 g)), ((nb078AlphaDummy410),
        (nb078AlphaDummy412 g)), ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
        ((nb078AlphaDummy439), (nb078AlphaDummy440 g)), ((nb078AlphaDummy413),
        (nb078AlphaDummy414 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
        ((nb078AlphaDummy649), (nb078AlphaDummy651 g)), ((nb078AlphaDummy653),
        (nb078AlphaDummy654 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
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
                                          (mem_lt_freshVar (nb078_support_mem_0459 g)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy650) from
                                    (by
                                      unfold nb078AlphaDummy650;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0758)
                                              1)))) (show g ≠ (nb078AlphaDummy652 g) from (by
                                      unfold nb078AlphaDummy652;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0759 g)
                                              1)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy001) ≠ (nb078AlphaDummy649) from (by
                                        unfold nb078AlphaDummy649;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0758)
                                                0)))) (show g ≠ (nb078AlphaDummy651 g) from
                                      (by
                                        unfold nb078AlphaDummy651;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0759 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy001) ≠ (nb078AlphaDummy653) from
                                        (by
                                          unfold nb078AlphaDummy653;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0756)
                                                  0)))) (show g ≠ (nb078AlphaDummy654 g) from
                                        (by
                                          unfold nb078AlphaDummy654;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0757 g) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy001) ≠
        (nb078AlphaDummy571) from (by
          unfold nb078AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0752) 2)))) (show g ≠ (nb078AlphaDummy574 g) from (by
          unfold nb078AlphaDummy574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0754 g) 2)))) (TAlphaVar.there (show
        (nb078AlphaDummy001) ≠ (nb078AlphaDummy570) from (by
          unfold nb078AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0752) 1)))) (show g ≠ (nb078AlphaDummy573 g) from (by
          unfold nb078AlphaDummy573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0754 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy001) ≠ (nb078AlphaDummy569) from (by
          unfold nb078AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0752) 0)))) (show g ≠ (nb078AlphaDummy572 g) from (by
          unfold nb078AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0754 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy001) ≠ (nb078AlphaDummy575) from (by
          unfold nb078AlphaDummy575;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0753) 0)))) (show g ≠ (nb078AlphaDummy576 g) from (by
          unfold nb078AlphaDummy576;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0755 g) 0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part119`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0095`. -/
@[expose]
noncomputable def nb078SplitAlpha0095 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy733), (nb078AlphaDummy734 g)),
        ((nb078AlphaDummy731), (nb078AlphaDummy732 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy733))
          (Class.cab (nb078AlphaDummy727)
            (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy571))
              (Wff.classEq (Class.cv (nb078AlphaDummy727))
                (synCphi (Class.cv (nb078AlphaDummy728))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy733)) (Class.cab (nb078AlphaDummy727)
              (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy571))
                (Wff.classEq (Class.cv (nb078AlphaDummy727))
                  (synCphi (Class.cv (nb078AlphaDummy728)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy734 g))
          (Class.cab (nb078AlphaDummy729 g)
            (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy574 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                (synCphi (Class.cv (nb078AlphaDummy730 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy734 g))
            (Class.cab (nb078AlphaDummy729 g)
              (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy574 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                  (synCphi (Class.cv (nb078AlphaDummy730 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy571) ≠ (nb078AlphaDummy728) from
                    (by
                      unfold nb078AlphaDummy728;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 1))))
                  (show (nb078AlphaDummy574 g) ≠ (nb078AlphaDummy730 g) from (by
                      unfold nb078AlphaDummy730;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0762 g) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy571) ≠ (nb078AlphaDummy727) from
                      (by
                        unfold nb078AlphaDummy727;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 0))))
                    (show (nb078AlphaDummy574 g) ≠ (nb078AlphaDummy729 g) from (by
                        unfold nb078AlphaDummy729;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0762 g) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy571) ≠ (nb078AlphaDummy733) from (by
                          unfold nb078AlphaDummy733;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0764) 0))))
                      (show (nb078AlphaDummy574 g) ≠ (nb078AlphaDummy734 g) from (by
                          unfold nb078AlphaDummy734;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0765 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy571) ≠ (nb078AlphaDummy731) from (by
                            unfold nb078AlphaDummy731;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0761) 0))))
                        (show (nb078AlphaDummy574 g) ≠ (nb078AlphaDummy732 g) from (by
                            unfold nb078AlphaDummy732;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0763 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy571))).fv ∪
                      ((Class.cv (nb078AlphaDummy570))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy574 g))).fv ∪
                      ((Class.cv (nb078AlphaDummy573 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy728) ≠ (nb078AlphaDummy735) from (by
                              unfold nb078AlphaDummy735;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0766) 0))))
                          (show (nb078AlphaDummy730 g) ≠ (nb078AlphaDummy737 g) from (by
                              unfold nb078AlphaDummy737;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0767 g) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy728) ≠ (nb078AlphaDummy736) from (by
                                unfold nb078AlphaDummy736;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0766) 1))))
                            (show (nb078AlphaDummy730 g) ≠ (nb078AlphaDummy738 g) from (by
                                unfold nb078AlphaDummy738;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0767 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy728))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy730 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy735) ≠ (nb078AlphaDummy742) from (by
          unfold nb078AlphaDummy742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0770) 1)))) (show (nb078AlphaDummy737 g) ≠
        (nb078AlphaDummy745 g) from (by
          unfold nb078AlphaDummy745;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0771 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy735) ≠ (nb078AlphaDummy741) from (by
          unfold nb078AlphaDummy741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0770) 0)))) (show (nb078AlphaDummy737 g) ≠
        (nb078AlphaDummy744 g) from (by
          unfold nb078AlphaDummy744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0771 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy735) ≠ (nb078AlphaDummy739) from (by
          unfold nb078AlphaDummy739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0768) 0)))) (show (nb078AlphaDummy737 g) ≠
        (nb078AlphaDummy740 g) from (by
          unfold nb078AlphaDummy740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0769 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy743), (nb078AlphaDummy746 g)), ((nb078AlphaDummy742),
        (nb078AlphaDummy745 g)), ((nb078AlphaDummy741), (nb078AlphaDummy744 g)),
        ((nb078AlphaDummy739), (nb078AlphaDummy740 g)), ((nb078AlphaDummy735),
        (nb078AlphaDummy737 g)), ((nb078AlphaDummy736), (nb078AlphaDummy738 g)),
        ((nb078AlphaDummy728), (nb078AlphaDummy730 g)), ((nb078AlphaDummy727),
        (nb078AlphaDummy729 g)), ((nb078AlphaDummy733), (nb078AlphaDummy734 g)),
        ((nb078AlphaDummy731), (nb078AlphaDummy732 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy749) from (by
          unfold
            nb078AlphaDummy749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0774)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy750 g) from (by
          unfold
            nb078AlphaDummy750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0775
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy747)
        from (by
          unfold
            nb078AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0772)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy748 g) from (by
          unfold
            nb078AlphaDummy748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0773
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy749)
        from (by
          unfold
            nb078AlphaDummy749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0778)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy750 g) from (by
          unfold
            nb078AlphaDummy750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0779
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy747)
        from (by
          unfold
            nb078AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0776)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy748 g) from (by
          unfold
            nb078AlphaDummy748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0777
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy749) from (by
          unfold
            nb078AlphaDummy749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0774)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy750 g) from (by
          unfold
            nb078AlphaDummy750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0775
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy747)
        from (by
          unfold
            nb078AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0772)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy748 g) from (by
          unfold
            nb078AlphaDummy748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0773
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy749)
        from (by
          unfold
            nb078AlphaDummy749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0778)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy750 g) from (by
          unfold
            nb078AlphaDummy750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0779
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy747)
        from (by
          unfold
            nb078AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0776)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy748 g) from (by
          unfold
            nb078AlphaDummy748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0777
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy743), (nb078AlphaDummy746 g)), ((nb078AlphaDummy742),
        (nb078AlphaDummy745 g)), ((nb078AlphaDummy741), (nb078AlphaDummy744 g)),
        ((nb078AlphaDummy739), (nb078AlphaDummy740 g)), ((nb078AlphaDummy735),
        (nb078AlphaDummy737 g)), ((nb078AlphaDummy736), (nb078AlphaDummy738 g)),
        ((nb078AlphaDummy728), (nb078AlphaDummy730 g)), ((nb078AlphaDummy727),
        (nb078AlphaDummy729 g)), ((nb078AlphaDummy733), (nb078AlphaDummy734 g)),
        ((nb078AlphaDummy731), (nb078AlphaDummy732 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy735))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy737
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy753) from (by
          unfold
            nb078AlphaDummy753;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0782)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy754 g) from (by
          unfold
            nb078AlphaDummy754;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0783
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy751)
        from (by
          unfold
            nb078AlphaDummy751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0780)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy752 g) from (by
          unfold
            nb078AlphaDummy752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0781
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy753)
        from (by
          unfold
            nb078AlphaDummy753;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0782)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy754 g) from (by
          unfold
            nb078AlphaDummy754;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0783
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy751)
        from (by
          unfold
            nb078AlphaDummy751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0780)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy752 g) from (by
          unfold
            nb078AlphaDummy752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0781
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy755) from (by
          unfold
            nb078AlphaDummy755;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0786)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy756 g) from (by
          unfold
            nb078AlphaDummy756;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0787
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy751)
        from (by
          unfold
            nb078AlphaDummy751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0784)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy752 g) from (by
          unfold
            nb078AlphaDummy752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0785
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy743) ≠
        (nb078AlphaDummy755) from (by
          unfold
            nb078AlphaDummy755;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0786)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy756 g) from (by
          unfold
            nb078AlphaDummy756;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0787
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy751)
        from (by
          unfold
            nb078AlphaDummy751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0784)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy752 g) from (by
          unfold
            nb078AlphaDummy752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0785
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy735) ≠ (nb078AlphaDummy739) from (by
                                        unfold nb078AlphaDummy739;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0768)
                                                0)))) (show (nb078AlphaDummy737 g) ≠
                                        (nb078AlphaDummy740 g) from (by
                                        unfold nb078AlphaDummy740;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0769 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy739), (nb078AlphaDummy740 g)),
                                    ((nb078AlphaDummy735), (nb078AlphaDummy737 g)),
                                    ((nb078AlphaDummy736), (nb078AlphaDummy738 g)),
                                    ((nb078AlphaDummy728), (nb078AlphaDummy730 g)),
                                    ((nb078AlphaDummy727), (nb078AlphaDummy729 g)),
                                    ((nb078AlphaDummy733), (nb078AlphaDummy734 g)),
                                    ((nb078AlphaDummy731), (nb078AlphaDummy732 g)),
                                    ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                    ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                    ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                    ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy735) ≠ (nb078AlphaDummy739) from
                                    (by
                                      unfold nb078AlphaDummy739;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0768)
                                              0)))) (show
                                    (nb078AlphaDummy737 g) ≠ (nb078AlphaDummy740 g) from
                                    (by
                                      unfold nb078AlphaDummy740;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0769 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy735) ≠ (nb078AlphaDummy739) from (by
                                        unfold nb078AlphaDummy739;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0768)
                                                0)))) (show (nb078AlphaDummy737 g) ≠
                                        (nb078AlphaDummy740 g) from (by
                                        unfold nb078AlphaDummy740;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0769 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy739), (nb078AlphaDummy740 g)),
                                    ((nb078AlphaDummy735), (nb078AlphaDummy737 g)),
                                    ((nb078AlphaDummy736), (nb078AlphaDummy738 g)),
                                    ((nb078AlphaDummy728), (nb078AlphaDummy730 g)),
                                    ((nb078AlphaDummy727), (nb078AlphaDummy729 g)),
                                    ((nb078AlphaDummy733), (nb078AlphaDummy734 g)),
                                    ((nb078AlphaDummy731), (nb078AlphaDummy732 g)),
                                    ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                    ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                    ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                    ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy571) ≠ (nb078AlphaDummy728) from
                      (by
                        unfold nb078AlphaDummy728;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 1))))
                    (show (nb078AlphaDummy574 g) ≠ (nb078AlphaDummy730 g) from (by
                        unfold nb078AlphaDummy730;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0762 g) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy571) ≠ (nb078AlphaDummy727) from (by
                          unfold nb078AlphaDummy727;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0760) 0))))
                      (show (nb078AlphaDummy574 g) ≠ (nb078AlphaDummy729 g) from (by
                          unfold nb078AlphaDummy729;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0762 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy571) ≠ (nb078AlphaDummy733) from (by
                            unfold nb078AlphaDummy733;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0764) 0))))
                        (show (nb078AlphaDummy574 g) ≠ (nb078AlphaDummy734 g) from (by
                            unfold nb078AlphaDummy734;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0765 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy571) ≠ (nb078AlphaDummy731) from (by
                              unfold nb078AlphaDummy731;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0761) 0))))
                          (show (nb078AlphaDummy574 g) ≠ (nb078AlphaDummy732 g) from (by
                              unfold nb078AlphaDummy732;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0763 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy571))).fv ∪
                        ((Class.cv (nb078AlphaDummy570))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy574 g))).fv ∪
                        ((Class.cv (nb078AlphaDummy573 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy728) ≠ (nb078AlphaDummy735) from (by
                                unfold nb078AlphaDummy735;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0766) 0))))
                            (show (nb078AlphaDummy730 g) ≠ (nb078AlphaDummy737 g) from (by
                                unfold nb078AlphaDummy737;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0767 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy728) ≠ (nb078AlphaDummy736) from (by
                                  unfold nb078AlphaDummy736;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0766) 1))))
                              (show (nb078AlphaDummy730 g) ≠ (nb078AlphaDummy738 g) from
                                (by
                                  unfold nb078AlphaDummy738;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0767 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy728))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy730 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy735) ≠ (nb078AlphaDummy742) from (by
          unfold nb078AlphaDummy742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0770) 1)))) (show (nb078AlphaDummy737 g) ≠
        (nb078AlphaDummy745 g) from (by
          unfold nb078AlphaDummy745;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0771 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy735) ≠ (nb078AlphaDummy741) from (by
          unfold nb078AlphaDummy741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0770) 0)))) (show (nb078AlphaDummy737 g) ≠
        (nb078AlphaDummy744 g) from (by
          unfold nb078AlphaDummy744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0771 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy735) ≠ (nb078AlphaDummy739)
        from (by
          unfold nb078AlphaDummy739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0768)
                  0)))) (show (nb078AlphaDummy737 g) ≠ (nb078AlphaDummy740 g) from (by
          unfold nb078AlphaDummy740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0769 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy743), (nb078AlphaDummy746 g)), ((nb078AlphaDummy742),
        (nb078AlphaDummy745 g)), ((nb078AlphaDummy741), (nb078AlphaDummy744 g)),
        ((nb078AlphaDummy739), (nb078AlphaDummy740 g)), ((nb078AlphaDummy735),
        (nb078AlphaDummy737 g)), ((nb078AlphaDummy736), (nb078AlphaDummy738 g)),
        ((nb078AlphaDummy728), (nb078AlphaDummy730 g)), ((nb078AlphaDummy727),
        (nb078AlphaDummy729 g)), ((nb078AlphaDummy733), (nb078AlphaDummy734 g)),
        ((nb078AlphaDummy731), (nb078AlphaDummy732 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy749) from (by
          unfold
            nb078AlphaDummy749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0774)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy750 g) from (by
          unfold
            nb078AlphaDummy750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0775
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy747)
        from (by
          unfold
            nb078AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0772)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy748 g) from (by
          unfold
            nb078AlphaDummy748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0773
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy749)
        from (by
          unfold
            nb078AlphaDummy749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0778)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy750 g) from (by
          unfold
            nb078AlphaDummy750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0779
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy747)
        from (by
          unfold
            nb078AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0776)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy748 g) from (by
          unfold
            nb078AlphaDummy748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0777
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy749) from (by
          unfold
            nb078AlphaDummy749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0774)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy750 g) from (by
          unfold
            nb078AlphaDummy750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0775
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy747)
        from (by
          unfold
            nb078AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0772)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy748 g) from (by
          unfold
            nb078AlphaDummy748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0773
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy749)
        from (by
          unfold
            nb078AlphaDummy749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0778)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy750 g) from (by
          unfold
            nb078AlphaDummy750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0779
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy747)
        from (by
          unfold
            nb078AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0776)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy748 g) from (by
          unfold
            nb078AlphaDummy748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0777
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy743), (nb078AlphaDummy746 g)), ((nb078AlphaDummy742),
        (nb078AlphaDummy745 g)), ((nb078AlphaDummy741), (nb078AlphaDummy744 g)),
        ((nb078AlphaDummy739), (nb078AlphaDummy740 g)), ((nb078AlphaDummy735),
        (nb078AlphaDummy737 g)), ((nb078AlphaDummy736), (nb078AlphaDummy738 g)),
        ((nb078AlphaDummy728), (nb078AlphaDummy730 g)), ((nb078AlphaDummy727),
        (nb078AlphaDummy729 g)), ((nb078AlphaDummy733), (nb078AlphaDummy734 g)),
        ((nb078AlphaDummy731), (nb078AlphaDummy732 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy735))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy737
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy753) from (by
          unfold
            nb078AlphaDummy753;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0782)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy754 g) from (by
          unfold
            nb078AlphaDummy754;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0783
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy751)
        from (by
          unfold
            nb078AlphaDummy751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0780)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy752 g) from (by
          unfold
            nb078AlphaDummy752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0781
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy753)
        from (by
          unfold
            nb078AlphaDummy753;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0782)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy754 g) from (by
          unfold
            nb078AlphaDummy754;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0783
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy751)
        from (by
          unfold
            nb078AlphaDummy751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0780)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy752 g) from (by
          unfold
            nb078AlphaDummy752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0781
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy755) from (by
          unfold
            nb078AlphaDummy755;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0786)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy756 g) from (by
          unfold
            nb078AlphaDummy756;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0787
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy751)
        from (by
          unfold
            nb078AlphaDummy751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0784)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy752 g) from (by
          unfold
            nb078AlphaDummy752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0785
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy743) ≠
        (nb078AlphaDummy755) from (by
          unfold
            nb078AlphaDummy755;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0786)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy756 g) from (by
          unfold
            nb078AlphaDummy756;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0787
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy751)
        from (by
          unfold
            nb078AlphaDummy751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0784)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy752 g) from (by
          unfold
            nb078AlphaDummy752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0785
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy735) ≠ (nb078AlphaDummy739) from
                                        (by
                                          unfold nb078AlphaDummy739;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0768)
                                                  0)))) (show (nb078AlphaDummy737 g) ≠
        (nb078AlphaDummy740 g) from (by
                                          unfold nb078AlphaDummy740;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0769 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy739), (nb078AlphaDummy740 g)),
                                      ((nb078AlphaDummy735), (nb078AlphaDummy737 g)),
                                      ((nb078AlphaDummy736), (nb078AlphaDummy738 g)),
                                      ((nb078AlphaDummy728), (nb078AlphaDummy730 g)),
                                      ((nb078AlphaDummy727), (nb078AlphaDummy729 g)),
                                      ((nb078AlphaDummy733), (nb078AlphaDummy734 g)),
                                      ((nb078AlphaDummy731), (nb078AlphaDummy732 g)),
                                      ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                      ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                      ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                      ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy735) ≠ (nb078AlphaDummy739) from (by
                                        unfold nb078AlphaDummy739;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0768)
                                                0)))) (show (nb078AlphaDummy737 g) ≠
                                        (nb078AlphaDummy740 g) from (by
                                        unfold nb078AlphaDummy740;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0769 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy735) ≠ (nb078AlphaDummy739) from
                                        (by
                                          unfold nb078AlphaDummy739;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0768)
                                                  0)))) (show (nb078AlphaDummy737 g) ≠
        (nb078AlphaDummy740 g) from (by
                                          unfold nb078AlphaDummy740;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0769 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy739), (nb078AlphaDummy740 g)),
                                      ((nb078AlphaDummy735), (nb078AlphaDummy737 g)),
                                      ((nb078AlphaDummy736), (nb078AlphaDummy738 g)),
                                      ((nb078AlphaDummy728), (nb078AlphaDummy730 g)),
                                      ((nb078AlphaDummy727), (nb078AlphaDummy729 g)),
                                      ((nb078AlphaDummy733), (nb078AlphaDummy734 g)),
                                      ((nb078AlphaDummy731), (nb078AlphaDummy732 g)),
                                      ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                      ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                      ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                      ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
