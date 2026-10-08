/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block025

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part085`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0056`. -/
@[expose]
noncomputable def nb078SplitAlpha0056 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy441), (nb078AlphaDummy442 g)),
        ((nb078AlphaDummy410), (nb078AlphaDummy412 g)),
        ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
        ((nb078AlphaDummy439), (nb078AlphaDummy440 g)),
        ((nb078AlphaDummy413), (nb078AlphaDummy414 g)),
        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
        ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
        ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy441))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy410))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy441)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy442 g))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy412 g))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy442 g))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy410) ≠ (nb078AlphaDummy417) from (by
                              unfold nb078AlphaDummy417;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0418) 0))))
                          (show (nb078AlphaDummy412 g) ≠ (nb078AlphaDummy419 g) from (by
                              unfold nb078AlphaDummy419;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0419 g) 0))))
                          (TAlphaVar.there
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
                              (show (nb078AlphaDummy412 g) ≠ (nb078AlphaDummy444 g) from
                                (by
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
                                          (mem_lt_freshVar (nb078_support_mem_0446) 0)))) (show
                                  (nb078AlphaDummy412 g) ≠ (nb078AlphaDummy442 g) from (by
                                    unfold nb078AlphaDummy442;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0447 g)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy410))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy412 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy417) ≠ (nb078AlphaDummy424) from (by
          unfold nb078AlphaDummy424;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0422) 1)))) (show (nb078AlphaDummy419 g) ≠
        (nb078AlphaDummy427 g) from (by
          unfold nb078AlphaDummy427;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0423 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy417) ≠ (nb078AlphaDummy423) from (by
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
                  (nb078_support_mem_0421 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
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
        ((nb078AlphaDummy482), (nb078AlphaDummy484 g)), ((nb078AlphaDummy481),
        (nb078AlphaDummy483 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078AlphaDummy482), (nb078AlphaDummy484 g)), ((nb078AlphaDummy481),
        (nb078AlphaDummy483 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy417))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy419
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy435) from (by
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
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from (by
                                        unfold nb078AlphaDummy421;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0420)
                                                0)))) (show (nb078AlphaDummy419 g) ≠
                                        (nb078AlphaDummy422 g) from (by
                                        unfold nb078AlphaDummy422;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0421 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
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
                                    ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
                                    ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from
                                    (by
                                      unfold nb078AlphaDummy421;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0420)
                                              0)))) (show
                                    (nb078AlphaDummy419 g) ≠ (nb078AlphaDummy422 g) from
                                    (by
                                      unfold nb078AlphaDummy422;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0421 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from (by
                                        unfold nb078AlphaDummy421;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0420)
                                                0)))) (show (nb078AlphaDummy419 g) ≠
                                        (nb078AlphaDummy422 g) from (by
                                        unfold nb078AlphaDummy422;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0421 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
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
                                    ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
                                    ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy410) ≠ (nb078AlphaDummy417) from (by
                              unfold nb078AlphaDummy417;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0418) 0))))
                          (show (nb078AlphaDummy412 g) ≠ (nb078AlphaDummy419 g) from (by
                              unfold nb078AlphaDummy419;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0419 g) 0))))
                          (TAlphaVar.there
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
                              (show (nb078AlphaDummy412 g) ≠ (nb078AlphaDummy444 g) from
                                (by
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
                                          (mem_lt_freshVar (nb078_support_mem_0446) 0)))) (show
                                  (nb078AlphaDummy412 g) ≠ (nb078AlphaDummy442 g) from (by
                                    unfold nb078AlphaDummy442;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0447 g)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy410))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy412 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy417) ≠ (nb078AlphaDummy424) from (by
          unfold nb078AlphaDummy424;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0422) 1)))) (show (nb078AlphaDummy419 g) ≠
        (nb078AlphaDummy427 g) from (by
          unfold nb078AlphaDummy427;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0423 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy417) ≠ (nb078AlphaDummy423) from (by
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
                  (nb078_support_mem_0421 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
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
        ((nb078AlphaDummy482), (nb078AlphaDummy484 g)), ((nb078AlphaDummy481),
        (nb078AlphaDummy483 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078AlphaDummy482), (nb078AlphaDummy484 g)), ((nb078AlphaDummy481),
        (nb078AlphaDummy483 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy417))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy419
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy435) from (by
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
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from (by
                                        unfold nb078AlphaDummy421;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0420)
                                                0)))) (show (nb078AlphaDummy419 g) ≠
                                        (nb078AlphaDummy422 g) from (by
                                        unfold nb078AlphaDummy422;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0421 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
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
                                    ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
                                    ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from
                                    (by
                                      unfold nb078AlphaDummy421;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0420)
                                              0)))) (show
                                    (nb078AlphaDummy419 g) ≠ (nb078AlphaDummy422 g) from
                                    (by
                                      unfold nb078AlphaDummy422;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0421 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from (by
                                        unfold nb078AlphaDummy421;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0420)
                                                0)))) (show (nb078AlphaDummy419 g) ≠
                                        (nb078AlphaDummy422 g) from (by
                                        unfold nb078AlphaDummy422;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0421 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
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
                                    ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
                                    ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy441), (nb078AlphaDummy442 g)),
            ((nb078AlphaDummy410), (nb078AlphaDummy412 g)),
            ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
            ((nb078AlphaDummy439), (nb078AlphaDummy440 g)),
            ((nb078AlphaDummy413), (nb078AlphaDummy414 g)),
            ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
            ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
            ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
            ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
            ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
            ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
            ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0057`. -/
@[expose]
noncomputable def nb078SplitAlpha0057 (x : Var) (y : Var) (g : Var) (dv_g_y : g ≠ y) :
    TAlphaWff
      [((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (synWfun (Class.cv (nb078AlphaDummy001))) (Wff.neg
          (Wff.classEq (synCdm (Class.cv (nb078AlphaDummy001)))
            (Class.cv (nb078AlphaDummy004)))))
      (Wff.imp (synWfun (Class.cv g))
        (Wff.neg (Wff.classEq (synCdm (Class.cv g)) (Class.cv y)))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex
                          (TAlphaWff.ex (TAlphaWff.neg (nb078SplitAlpha0040 x y g))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn
                        [((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
                          ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
                          ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                          ((nb078AlphaDummy003), x)]
                        (synCid) (nb078WppRefl0136 x y g)))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex
                          (TAlphaWff.ex (TAlphaWff.neg (nb078SplitAlpha0040 x y g))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn
                        [((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
                          ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
                          ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                          ((nb078AlphaDummy003), x)]
                        (synCid) (nb078WppRefl0136 x y g)))))))))) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (Ne.symm
                      (show (nb078AlphaDummy288) ≠ (nb078AlphaDummy293) from (by
                          unfold nb078AlphaDummy293;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0292) 0))))) (Ne.symm
                      (show (nb078AlphaDummy291 g) ≠ (nb078AlphaDummy294 g) from (by
                          unfold nb078AlphaDummy294;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0293 g) 0)))))
                    (TAlphaVar.there (Ne.symm
                        (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy293) from (by
                            unfold nb078AlphaDummy293;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0290) 0))))) (Ne.symm
                        (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy294 g) from (by
                            unfold nb078AlphaDummy294;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0291 g) 0)))))
                      (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0041 x y g)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb078SplitAlpha0042 x y g)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                      (nb078SplitAlpha0042 x y g))))))))))))) (TAlphaWff.ex
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb078SplitAlpha0043 x y g)))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy289) ≠ (nb078AlphaDummy332) from (by
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
                  (nb078_support_mem_0362 g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy331)
        from (by
          unfold nb078AlphaDummy331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0360)
                  0)))) (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy333 g) from (by
          unfold nb078AlphaDummy333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0362 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy361)
        from (by
          unfold nb078AlphaDummy361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0364)
                  0)))) (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy362 g) from (by
          unfold nb078AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0365 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy335)
        from (by
          unfold nb078AlphaDummy335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0361)
                  0)))) (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy336 g) from (by
          unfold nb078AlphaDummy336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0363
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy287))).fv ∪
        ((Class.cv (nb078AlphaDummy289))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy290 g))).fv ∪ ((Class.cv (nb078AlphaDummy292 g))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078SplitAlpha0044 x y g)))))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy332) from (by
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
                  (nb078_support_mem_0362 g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy331)
        from (by
          unfold nb078AlphaDummy331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0360)
                  0)))) (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy333 g) from (by
          unfold nb078AlphaDummy333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0362 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy361)
        from (by
          unfold nb078AlphaDummy361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0364)
                  0)))) (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy362 g) from (by
          unfold nb078AlphaDummy362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0365 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy335)
        from (by
          unfold nb078AlphaDummy335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0361)
                  0)))) (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy336 g) from (by
          unfold nb078AlphaDummy336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0363
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy287))).fv ∪
        ((Class.cv (nb078AlphaDummy289))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy290 g))).fv ∪ ((Class.cv (nb078AlphaDummy292 g))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078SplitAlpha0044 x y g))))))))))))))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                      (nb078AlphaDummy368) ≠ (nb078AlphaDummy371) from (by
                                        unfold nb078AlphaDummy371;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0372)
                                                0))))) (Ne.symm (show
                                      (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy372 g) from
                                      (by
                                        unfold nb078AlphaDummy372;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0373 g)
                                                0))))) (TAlphaVar.there (Ne.symm (show
                                        (nb078AlphaDummy367) ≠ (nb078AlphaDummy371) from
                                        (by
                                          unfold nb078AlphaDummy371;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0370)
                                                  0))))) (Ne.symm (show
                                        (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy372 g)
                                        from (by
                                          unfold nb078AlphaDummy372;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0371 g) 0)))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb078SplitAlpha0045 x y g))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy374) from (by
          unfold
            nb078AlphaDummy374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0402)
                  1)))) (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy376 g) from (by
          unfold
            nb078AlphaDummy376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0404
                    g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy373)
        from (by
          unfold
            nb078AlphaDummy373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0402)
                  0)))) (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy375 g) from (by
          unfold
            nb078AlphaDummy375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0404
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy403)
        from (by
          unfold
            nb078AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0406)
                  0)))) (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy404 g) from (by
          unfold
            nb078AlphaDummy404;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0046 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy405), (nb078AlphaDummy406 g)), ((nb078AlphaDummy374),
        (nb078AlphaDummy376 g)), ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
        ((nb078AlphaDummy403), (nb078AlphaDummy404 g)), ((nb078AlphaDummy377),
        (nb078AlphaDummy378 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)), ((nb078AlphaDummy287),
        (nb078AlphaDummy290 g)), ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y), ((nb078AlphaDummy003),
        x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy368) ≠
        (nb078AlphaDummy374) from (by
          unfold
            nb078AlphaDummy374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0402)
                  1)))) (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy376 g) from (by
          unfold
            nb078AlphaDummy376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0404
                    g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy373)
        from (by
          unfold
            nb078AlphaDummy373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0402)
                  0)))) (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy375 g) from (by
          unfold
            nb078AlphaDummy375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0404
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy403)
        from (by
          unfold
            nb078AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0406)
                  0)))) (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy404 g) from (by
          unfold
            nb078AlphaDummy404;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0046 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy405), (nb078AlphaDummy406 g)), ((nb078AlphaDummy374),
        (nb078AlphaDummy376 g)), ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
        ((nb078AlphaDummy403), (nb078AlphaDummy404 g)), ((nb078AlphaDummy377),
        (nb078AlphaDummy378 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)), ((nb078AlphaDummy287),
        (nb078AlphaDummy290 g)), ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y), ((nb078AlphaDummy003),
        x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb078SplitAlpha0047 x y g))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy410) from (by
          unfold
            nb078AlphaDummy410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0440)
                  1)))) (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy412 g) from (by
          unfold
            nb078AlphaDummy412;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0442
                    g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy409)
        from (by
          unfold
            nb078AlphaDummy409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0440)
                  0)))) (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy411 g) from (by
          unfold
            nb078AlphaDummy411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0442
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy439)
        from (by
          unfold
            nb078AlphaDummy439;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0444)
                  0)))) (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy440 g) from (by
          unfold
            nb078AlphaDummy440;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0048 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy441), (nb078AlphaDummy442 g)), ((nb078AlphaDummy410),
        (nb078AlphaDummy412 g)), ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
        ((nb078AlphaDummy439), (nb078AlphaDummy440 g)), ((nb078AlphaDummy413),
        (nb078AlphaDummy414 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)), ((nb078AlphaDummy287),
        (nb078AlphaDummy290 g)), ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y), ((nb078AlphaDummy003),
        x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy367) ≠
        (nb078AlphaDummy410) from (by
          unfold
            nb078AlphaDummy410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0440)
                  1)))) (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy412 g) from (by
          unfold
            nb078AlphaDummy412;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0442
                    g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy409)
        from (by
          unfold
            nb078AlphaDummy409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0440)
                  0)))) (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy411 g) from (by
          unfold
            nb078AlphaDummy411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0442
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy439)
        from (by
          unfold
            nb078AlphaDummy439;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0444)
                  0)))) (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy440 g) from (by
          unfold
            nb078AlphaDummy440;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0048 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy441), (nb078AlphaDummy442 g)), ((nb078AlphaDummy410),
        (nb078AlphaDummy412 g)), ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
        ((nb078AlphaDummy439), (nb078AlphaDummy440 g)), ((nb078AlphaDummy413),
        (nb078AlphaDummy414 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)), ((nb078AlphaDummy287),
        (nb078AlphaDummy290 g)), ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y), ((nb078AlphaDummy003),
        x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy368) from
                                    (by
                                      unfold nb078AlphaDummy368;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0460)
                                              1)))) (show g ≠ (nb078AlphaDummy370 g) from (by
                                      unfold nb078AlphaDummy370;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0461 g)
                                              1)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy001) ≠ (nb078AlphaDummy367) from (by
                                        unfold nb078AlphaDummy367;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0460)
                                                0)))) (show g ≠ (nb078AlphaDummy369 g) from
                                      (by
                                        unfold nb078AlphaDummy369;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0461 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy001) ≠ (nb078AlphaDummy371) from
                                        (by
                                          unfold nb078AlphaDummy371;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0458)
                                                  0)))) (show g ≠ (nb078AlphaDummy372 g) from
                                        (by
                                          unfold nb078AlphaDummy372;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0459 g) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy001) ≠
        (nb078AlphaDummy289) from (by
          unfold nb078AlphaDummy289;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0454) 2)))) (show g ≠ (nb078AlphaDummy292 g) from (by
          unfold nb078AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0456 g) 2)))) (TAlphaVar.there (show
        (nb078AlphaDummy001) ≠ (nb078AlphaDummy288) from (by
          unfold nb078AlphaDummy288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0454) 1)))) (show g ≠ (nb078AlphaDummy291 g) from (by
          unfold nb078AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0456 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy001) ≠ (nb078AlphaDummy287) from (by
          unfold nb078AlphaDummy287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0454) 0)))) (show g ≠ (nb078AlphaDummy290 g) from (by
          unfold nb078AlphaDummy290;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0456 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy001) ≠ (nb078AlphaDummy293) from (by
          unfold nb078AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0455) 0)))) (show g ≠ (nb078AlphaDummy294 g) from (by
          unfold nb078AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0457 g) 0)))) (TAlphaVar.here _ _ _)))))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb078SplitAlpha0049 x y g)))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy288) ≠ (nb078AlphaDummy446) from (by
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
                  (nb078_support_mem_0492 g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy288) ≠ (nb078AlphaDummy445)
        from (by
          unfold nb078AlphaDummy445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0490)
                  0)))) (show (nb078AlphaDummy291 g) ≠ (nb078AlphaDummy447 g) from (by
          unfold nb078AlphaDummy447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0492 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy288) ≠ (nb078AlphaDummy475)
        from (by
          unfold nb078AlphaDummy475;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0494)
                  0)))) (show (nb078AlphaDummy291 g) ≠ (nb078AlphaDummy476 g) from (by
          unfold nb078AlphaDummy476;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0495 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy288) ≠ (nb078AlphaDummy449)
        from (by
          unfold nb078AlphaDummy449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0491)
                  0)))) (show (nb078AlphaDummy291 g) ≠ (nb078AlphaDummy450 g) from (by
          unfold nb078AlphaDummy450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0493
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy001))).fv ∪ ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv)
        (by decide)) (freshVar_injective (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy289))).fv ∪
        ((Class.cv (nb078AlphaDummy288))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy292 g))).fv ∪ ((Class.cv (nb078AlphaDummy291 g))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078SplitAlpha0050 x y g)))))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy288) ≠ (nb078AlphaDummy446) from (by
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
                  (nb078_support_mem_0492 g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy288) ≠ (nb078AlphaDummy445)
        from (by
          unfold nb078AlphaDummy445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0490)
                  0)))) (show (nb078AlphaDummy291 g) ≠ (nb078AlphaDummy447 g) from (by
          unfold nb078AlphaDummy447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0492 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy288) ≠ (nb078AlphaDummy475)
        from (by
          unfold nb078AlphaDummy475;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0494)
                  0)))) (show (nb078AlphaDummy291 g) ≠ (nb078AlphaDummy476 g) from (by
          unfold nb078AlphaDummy476;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0495 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy288) ≠ (nb078AlphaDummy449)
        from (by
          unfold nb078AlphaDummy449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0491)
                  0)))) (show (nb078AlphaDummy291 g) ≠ (nb078AlphaDummy450 g) from (by
          unfold nb078AlphaDummy450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0493
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy001))).fv ∪ ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv)
        (by decide)) (freshVar_injective (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy289))).fv ∪
        ((Class.cv (nb078AlphaDummy288))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy292 g))).fv ∪ ((Class.cv (nb078AlphaDummy291 g))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078SplitAlpha0050 x y g))))))))))))))
                    (TAlphaClass.cv (TAlphaVar.there
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
                                  (mem_lt_freshVar (nb078_support_mem_0456 g) 2))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy288) from (by
                              unfold nb078AlphaDummy288;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0454) 1))))
                          (show g ≠ (nb078AlphaDummy291 g) from (by
                              unfold nb078AlphaDummy291;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0456 g) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy287) from (by
                                unfold nb078AlphaDummy287;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0454) 0))))
                            (show g ≠ (nb078AlphaDummy290 g) from (by
                                unfold nb078AlphaDummy290;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0456 g) 0))))
                            (TAlphaVar.there
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
                              (TAlphaVar.here _ _ _)))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
                    ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                    ((nb078AlphaDummy003), x)] (synCvv) (by simp only [fv_syn_cvv])))
              (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0052 x y g))))
                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                          (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                                (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy371) from (by
                                    unfold nb078AlphaDummy371;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0372) 0)))))
                              (Ne.symm (show
                                  (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy372 g) from (by
                                    unfold nb078AlphaDummy372;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0373 g)
                                            0))))) (TAlphaVar.there (Ne.symm
                                  (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy371) from
                                    (by
                                      unfold nb078AlphaDummy371;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0370)
                                              0))))) (Ne.symm (show
                                    (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy372 g) from
                                    (by
                                      unfold nb078AlphaDummy372;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0371 g)
                                              0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg
                                      (TAlphaWff.neg (nb078SplitAlpha0053 x y g)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                  (nb078_support_mem_0404
                    g)
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
          unfold
            nb078AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0406)
                  0)))) (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy404 g) from (by
          unfold
            nb078AlphaDummy404;
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
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078SplitAlpha0054 x y g))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                  (nb078_support_mem_0404
                    g)
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
          unfold
            nb078AlphaDummy403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0406)
                  0)))) (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy404 g) from (by
          unfold
            nb078AlphaDummy404;
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
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078SplitAlpha0054 x y g))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg
                                      (TAlphaWff.neg (nb078SplitAlpha0055 x y g)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                  (nb078_support_mem_0442
                    g)
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
          unfold
            nb078AlphaDummy439;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0444)
                  0)))) (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy440 g) from (by
          unfold
            nb078AlphaDummy440;
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
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078SplitAlpha0056 x y g))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                  (nb078_support_mem_0442
                    g)
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
          unfold
            nb078AlphaDummy439;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0444)
                  0)))) (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy440 g) from (by
          unfold
            nb078AlphaDummy440;
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
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078SplitAlpha0056 x y g)))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
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
                                          (mem_lt_freshVar (nb078_support_mem_0461 g)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy371) from
                                    (by
                                      unfold nb078AlphaDummy371;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0458)
                                              0)))) (show g ≠ (nb078AlphaDummy372 g) from (by
                                      unfold nb078AlphaDummy372;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0459 g)
                                              0)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy001) ≠ (nb078AlphaDummy482) from (by
                                        unfold nb078AlphaDummy482;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0538)
                                                1)))) (show g ≠ (nb078AlphaDummy484 g) from
                                      (by
                                        unfold nb078AlphaDummy484;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0539 g)
                                                1)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy001) ≠ (nb078AlphaDummy481) from
                                        (by
                                          unfold nb078AlphaDummy481;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0538)
                                                  0)))) (show g ≠ (nb078AlphaDummy483 g) from
                                        (by
                                          unfold nb078AlphaDummy483;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0539 g) 0))))
                                      (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
            (Ne.symm dv_g_y) (TAlphaVar.here _ _ _))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part086`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0058`. -/
@[expose]
noncomputable def nb078SplitAlpha0058 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy535), (nb078AlphaDummy536 g)),
        ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
        ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
        ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
        ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)),
        ((nb078AlphaDummy521), (nb078AlphaDummy522 x g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy535))
          (Class.cab (nb078AlphaDummy529)
            (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy526))
              (Wff.classEq (Class.cv (nb078AlphaDummy529))
                (synCphi (Class.cv (nb078AlphaDummy530))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy535)) (Class.cab (nb078AlphaDummy529)
              (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy526))
                (Wff.classEq (Class.cv (nb078AlphaDummy529))
                  (synCphi (Class.cv (nb078AlphaDummy530)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy536 g))
          (Class.cab (nb078AlphaDummy531 g)
            (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy528 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                (synCphi (Class.cv (nb078AlphaDummy532 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy536 g))
            (Class.cab (nb078AlphaDummy531 g)
              (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy528 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                  (synCphi (Class.cv (nb078AlphaDummy532 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy526) ≠ (nb078AlphaDummy530) from
                    (by
                      unfold nb078AlphaDummy530;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 1))))
                  (show (nb078AlphaDummy528 g) ≠ (nb078AlphaDummy532 g) from (by
                      unfold nb078AlphaDummy532;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0542 g) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy526) ≠ (nb078AlphaDummy529) from
                      (by
                        unfold nb078AlphaDummy529;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 0))))
                    (show (nb078AlphaDummy528 g) ≠ (nb078AlphaDummy531 g) from (by
                        unfold nb078AlphaDummy531;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0542 g) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy526) ≠ (nb078AlphaDummy535) from (by
                          unfold nb078AlphaDummy535;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0544) 0))))
                      (show (nb078AlphaDummy528 g) ≠ (nb078AlphaDummy536 g) from (by
                          unfold nb078AlphaDummy536;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0545 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy526) ≠ (nb078AlphaDummy533) from (by
                            unfold nb078AlphaDummy533;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0541) 0))))
                        (show (nb078AlphaDummy528 g) ≠ (nb078AlphaDummy534 g) from (by
                            unfold nb078AlphaDummy534;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0543 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy526))).fv ∪
                      ((Class.cv (nb078AlphaDummy525))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy528 g))).fv ∪
                      ((Class.cv (nb078AlphaDummy527 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy530) ≠ (nb078AlphaDummy537) from (by
                              unfold nb078AlphaDummy537;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0546) 0))))
                          (show (nb078AlphaDummy532 g) ≠ (nb078AlphaDummy539 g) from (by
                              unfold nb078AlphaDummy539;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0547 g) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy530) ≠ (nb078AlphaDummy538) from (by
                                unfold nb078AlphaDummy538;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0546) 1))))
                            (show (nb078AlphaDummy532 g) ≠ (nb078AlphaDummy540 g) from (by
                                unfold nb078AlphaDummy540;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0547 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy530))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy532 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy544) from (by
          unfold nb078AlphaDummy544;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550) 1)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy547 g) from (by
          unfold nb078AlphaDummy547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy537) ≠ (nb078AlphaDummy543) from (by
          unfold nb078AlphaDummy543;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550) 0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy546 g) from (by
          unfold nb078AlphaDummy546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from (by
          unfold nb078AlphaDummy541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548) 0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy542 g) from (by
          unfold nb078AlphaDummy542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy545), (nb078AlphaDummy548 g)), ((nb078AlphaDummy544),
        (nb078AlphaDummy547 g)), ((nb078AlphaDummy543), (nb078AlphaDummy546 g)),
        ((nb078AlphaDummy541), (nb078AlphaDummy542 g)), ((nb078AlphaDummy537),
        (nb078AlphaDummy539 g)), ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
        ((nb078AlphaDummy530), (nb078AlphaDummy532 g)), ((nb078AlphaDummy529),
        (nb078AlphaDummy531 g)), ((nb078AlphaDummy535), (nb078AlphaDummy536 g)),
        ((nb078AlphaDummy533), (nb078AlphaDummy534 g)), ((nb078AlphaDummy526),
        (nb078AlphaDummy528 g)), ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
        ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)), ((nb078AlphaDummy521),
        (nb078AlphaDummy522 x g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0554)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0555
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0552)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0553
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy551)
        from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0558)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0559
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0556)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0557
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0554)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0555
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0552)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0553
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy551)
        from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0558)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0559
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0556)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0557
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy545), (nb078AlphaDummy548 g)), ((nb078AlphaDummy544),
        (nb078AlphaDummy547 g)), ((nb078AlphaDummy543), (nb078AlphaDummy546 g)),
        ((nb078AlphaDummy541), (nb078AlphaDummy542 g)), ((nb078AlphaDummy537),
        (nb078AlphaDummy539 g)), ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
        ((nb078AlphaDummy530), (nb078AlphaDummy532 g)), ((nb078AlphaDummy529),
        (nb078AlphaDummy531 g)), ((nb078AlphaDummy535), (nb078AlphaDummy536 g)),
        ((nb078AlphaDummy533), (nb078AlphaDummy534 g)), ((nb078AlphaDummy526),
        (nb078AlphaDummy528 g)), ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
        ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)), ((nb078AlphaDummy521),
        (nb078AlphaDummy522 x g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy537))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539 g))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy544) ≠
        (nb078AlphaDummy555) from (by
          unfold
            nb078AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0562)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy556 g) from (by
          unfold
            nb078AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0563
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0560)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0561
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy555)
        from (by
          unfold
            nb078AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0562)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy556 g) from (by
          unfold
            nb078AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0563
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0560)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0561
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy557) from (by
          unfold
            nb078AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0566)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy558 g) from (by
          unfold
            nb078AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0567
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0564)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0565
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠
        (nb078AlphaDummy557) from (by
          unfold
            nb078AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0566)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy558 g) from (by
          unfold
            nb078AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0567
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0564)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0565
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from (by
                                        unfold nb078AlphaDummy541;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0548)
                                                0)))) (show (nb078AlphaDummy539 g) ≠
                                        (nb078AlphaDummy542 g) from (by
                                        unfold nb078AlphaDummy542;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0549 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy541), (nb078AlphaDummy542 g)),
                                    ((nb078AlphaDummy537), (nb078AlphaDummy539 g)),
                                    ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
                                    ((nb078AlphaDummy530), (nb078AlphaDummy532 g)),
                                    ((nb078AlphaDummy529), (nb078AlphaDummy531 g)),
                                    ((nb078AlphaDummy535), (nb078AlphaDummy536 g)),
                                    ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
                                    ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
                                    ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
                                    ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)),
                                    ((nb078AlphaDummy521), (nb078AlphaDummy522 x g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from
                                    (by
                                      unfold nb078AlphaDummy541;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0548)
                                              0)))) (show
                                    (nb078AlphaDummy539 g) ≠ (nb078AlphaDummy542 g) from
                                    (by
                                      unfold nb078AlphaDummy542;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0549 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from (by
                                        unfold nb078AlphaDummy541;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0548)
                                                0)))) (show (nb078AlphaDummy539 g) ≠
                                        (nb078AlphaDummy542 g) from (by
                                        unfold nb078AlphaDummy542;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0549 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy541), (nb078AlphaDummy542 g)),
                                    ((nb078AlphaDummy537), (nb078AlphaDummy539 g)),
                                    ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
                                    ((nb078AlphaDummy530), (nb078AlphaDummy532 g)),
                                    ((nb078AlphaDummy529), (nb078AlphaDummy531 g)),
                                    ((nb078AlphaDummy535), (nb078AlphaDummy536 g)),
                                    ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
                                    ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
                                    ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
                                    ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)),
                                    ((nb078AlphaDummy521), (nb078AlphaDummy522 x g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy526) ≠ (nb078AlphaDummy530) from
                      (by
                        unfold nb078AlphaDummy530;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 1))))
                    (show (nb078AlphaDummy528 g) ≠ (nb078AlphaDummy532 g) from (by
                        unfold nb078AlphaDummy532;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0542 g) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy526) ≠ (nb078AlphaDummy529) from (by
                          unfold nb078AlphaDummy529;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0540) 0))))
                      (show (nb078AlphaDummy528 g) ≠ (nb078AlphaDummy531 g) from (by
                          unfold nb078AlphaDummy531;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0542 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy526) ≠ (nb078AlphaDummy535) from (by
                            unfold nb078AlphaDummy535;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0544) 0))))
                        (show (nb078AlphaDummy528 g) ≠ (nb078AlphaDummy536 g) from (by
                            unfold nb078AlphaDummy536;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0545 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy526) ≠ (nb078AlphaDummy533) from (by
                              unfold nb078AlphaDummy533;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0541) 0))))
                          (show (nb078AlphaDummy528 g) ≠ (nb078AlphaDummy534 g) from (by
                              unfold nb078AlphaDummy534;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0543 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy526))).fv ∪
                        ((Class.cv (nb078AlphaDummy525))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy528 g))).fv ∪
                        ((Class.cv (nb078AlphaDummy527 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy530) ≠ (nb078AlphaDummy537) from (by
                                unfold nb078AlphaDummy537;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0546) 0))))
                            (show (nb078AlphaDummy532 g) ≠ (nb078AlphaDummy539 g) from (by
                                unfold nb078AlphaDummy539;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0547 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy530) ≠ (nb078AlphaDummy538) from (by
                                  unfold nb078AlphaDummy538;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0546) 1))))
                              (show (nb078AlphaDummy532 g) ≠ (nb078AlphaDummy540 g) from
                                (by
                                  unfold nb078AlphaDummy540;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0547 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy530))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy532 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy537) ≠ (nb078AlphaDummy544) from (by
          unfold nb078AlphaDummy544;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550) 1)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy547 g) from (by
          unfold nb078AlphaDummy547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy537) ≠ (nb078AlphaDummy543) from (by
          unfold nb078AlphaDummy543;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550) 0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy546 g) from (by
          unfold nb078AlphaDummy546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy541)
        from (by
          unfold nb078AlphaDummy541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548)
                  0)))) (show (nb078AlphaDummy539 g) ≠ (nb078AlphaDummy542 g) from (by
          unfold nb078AlphaDummy542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy545), (nb078AlphaDummy548 g)), ((nb078AlphaDummy544),
        (nb078AlphaDummy547 g)), ((nb078AlphaDummy543), (nb078AlphaDummy546 g)),
        ((nb078AlphaDummy541), (nb078AlphaDummy542 g)), ((nb078AlphaDummy537),
        (nb078AlphaDummy539 g)), ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
        ((nb078AlphaDummy530), (nb078AlphaDummy532 g)), ((nb078AlphaDummy529),
        (nb078AlphaDummy531 g)), ((nb078AlphaDummy535), (nb078AlphaDummy536 g)),
        ((nb078AlphaDummy533), (nb078AlphaDummy534 g)), ((nb078AlphaDummy526),
        (nb078AlphaDummy528 g)), ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
        ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)), ((nb078AlphaDummy521),
        (nb078AlphaDummy522 x g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0554)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0555
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0552)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0553
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy551)
        from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0558)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0559
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0556)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0557
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0554)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0555
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0552)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0553
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy551)
        from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0558)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0559
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0556)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0557
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy545), (nb078AlphaDummy548 g)), ((nb078AlphaDummy544),
        (nb078AlphaDummy547 g)), ((nb078AlphaDummy543), (nb078AlphaDummy546 g)),
        ((nb078AlphaDummy541), (nb078AlphaDummy542 g)), ((nb078AlphaDummy537),
        (nb078AlphaDummy539 g)), ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
        ((nb078AlphaDummy530), (nb078AlphaDummy532 g)), ((nb078AlphaDummy529),
        (nb078AlphaDummy531 g)), ((nb078AlphaDummy535), (nb078AlphaDummy536 g)),
        ((nb078AlphaDummy533), (nb078AlphaDummy534 g)), ((nb078AlphaDummy526),
        (nb078AlphaDummy528 g)), ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
        ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)), ((nb078AlphaDummy521),
        (nb078AlphaDummy522 x g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy537))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy544) ≠
        (nb078AlphaDummy555) from (by
          unfold
            nb078AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0562)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy556 g) from (by
          unfold
            nb078AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0563
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0560)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0561
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy555)
        from (by
          unfold
            nb078AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0562)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy556 g) from (by
          unfold
            nb078AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0563
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0560)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0561
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy557) from (by
          unfold
            nb078AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0566)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy558 g) from (by
          unfold
            nb078AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0567
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0564)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0565
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠
        (nb078AlphaDummy557) from (by
          unfold
            nb078AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0566)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy558 g) from (by
          unfold
            nb078AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0567
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0564)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0565
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from
                                        (by
                                          unfold nb078AlphaDummy541;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0548)
                                                  0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy542 g) from (by
                                          unfold nb078AlphaDummy542;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0549 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy541), (nb078AlphaDummy542 g)),
                                      ((nb078AlphaDummy537), (nb078AlphaDummy539 g)),
                                      ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
                                      ((nb078AlphaDummy530), (nb078AlphaDummy532 g)),
                                      ((nb078AlphaDummy529), (nb078AlphaDummy531 g)),
                                      ((nb078AlphaDummy535), (nb078AlphaDummy536 g)),
                                      ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
                                      ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
                                      ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
                                      ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)),
                                      ((nb078AlphaDummy521), (nb078AlphaDummy522 x g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from (by
                                        unfold nb078AlphaDummy541;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0548)
                                                0)))) (show (nb078AlphaDummy539 g) ≠
                                        (nb078AlphaDummy542 g) from (by
                                        unfold nb078AlphaDummy542;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0549 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from
                                        (by
                                          unfold nb078AlphaDummy541;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0548)
                                                  0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy542 g) from (by
                                          unfold nb078AlphaDummy542;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0549 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy541), (nb078AlphaDummy542 g)),
                                      ((nb078AlphaDummy537), (nb078AlphaDummy539 g)),
                                      ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
                                      ((nb078AlphaDummy530), (nb078AlphaDummy532 g)),
                                      ((nb078AlphaDummy529), (nb078AlphaDummy531 g)),
                                      ((nb078AlphaDummy535), (nb078AlphaDummy536 g)),
                                      ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
                                      ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
                                      ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
                                      ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)),
                                      ((nb078AlphaDummy521), (nb078AlphaDummy522 x g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
