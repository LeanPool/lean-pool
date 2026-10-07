/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block040

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part123`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0099`. -/
@[expose]
noncomputable def nb078SplitAlpha0099 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy415), (nb078AlphaDummy416 g)),
        ((nb078AlphaDummy413), (nb078AlphaDummy414 g)),
        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy415))
          (Class.cab (nb078AlphaDummy409)
            (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy368))
              (Wff.classEq (Class.cv (nb078AlphaDummy409))
                (synCphi (Class.cv (nb078AlphaDummy410))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy415)) (Class.cab (nb078AlphaDummy409)
              (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy368))
                (Wff.classEq (Class.cv (nb078AlphaDummy409))
                  (synCphi (Class.cv (nb078AlphaDummy410)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy416 g))
          (Class.cab (nb078AlphaDummy411 g)
            (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy370 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                (synCphi (Class.cv (nb078AlphaDummy412 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy416 g))
            (Class.cab (nb078AlphaDummy411 g)
              (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy370 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                  (synCphi (Class.cv (nb078AlphaDummy412 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy410) from
                    (by
                      unfold nb078AlphaDummy410;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 1))))
                  (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy412 g) from (by
                      unfold nb078AlphaDummy412;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0414 g) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy409) from
                      (by
                        unfold nb078AlphaDummy409;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 0))))
                    (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy411 g) from (by
                        unfold nb078AlphaDummy411;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0414 g) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy415) from (by
                          unfold nb078AlphaDummy415;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0416) 0))))
                      (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy416 g) from (by
                          unfold nb078AlphaDummy416;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0417 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy413) from (by
                            unfold nb078AlphaDummy413;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0413) 0))))
                        (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy414 g) from (by
                            unfold nb078AlphaDummy414;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0415 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy368))).fv ∪
                      ((Class.cv (nb078AlphaDummy367))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy370 g))).fv ∪
                      ((Class.cv (nb078AlphaDummy369 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
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
        ((nb078AlphaDummy410), (nb078AlphaDummy412 g)), ((nb078AlphaDummy409),
        (nb078AlphaDummy411 g)), ((nb078AlphaDummy415), (nb078AlphaDummy416 g)),
        ((nb078AlphaDummy413), (nb078AlphaDummy414 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
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
        ((nb078AlphaDummy410), (nb078AlphaDummy412 g)), ((nb078AlphaDummy409),
        (nb078AlphaDummy411 g)), ((nb078AlphaDummy415), (nb078AlphaDummy416 g)),
        ((nb078AlphaDummy413), (nb078AlphaDummy414 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
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
                                    ((nb078AlphaDummy410), (nb078AlphaDummy412 g)),
                                    ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
                                    ((nb078AlphaDummy415), (nb078AlphaDummy416 g)),
                                    ((nb078AlphaDummy413), (nb078AlphaDummy414 g)),
                                    ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                    ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                    ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                                    ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                    ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                    ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                    ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
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
                                    ((nb078AlphaDummy410), (nb078AlphaDummy412 g)),
                                    ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
                                    ((nb078AlphaDummy415), (nb078AlphaDummy416 g)),
                                    ((nb078AlphaDummy413), (nb078AlphaDummy414 g)),
                                    ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                    ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                    ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
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
                  (TAlphaVar.there (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy410) from
                      (by
                        unfold nb078AlphaDummy410;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 1))))
                    (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy412 g) from (by
                        unfold nb078AlphaDummy412;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0414 g) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy409) from (by
                          unfold nb078AlphaDummy409;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0412) 0))))
                      (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy411 g) from (by
                          unfold nb078AlphaDummy411;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0414 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy415) from (by
                            unfold nb078AlphaDummy415;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0416) 0))))
                        (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy416 g) from (by
                            unfold nb078AlphaDummy416;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0417 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy413) from (by
                              unfold nb078AlphaDummy413;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0413) 0))))
                          (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy414 g) from (by
                              unfold nb078AlphaDummy414;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0415 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy368))).fv ∪
                        ((Class.cv (nb078AlphaDummy367))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy370 g))).fv ∪
                        ((Class.cv (nb078AlphaDummy369 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
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
                              (show (nb078AlphaDummy412 g) ≠ (nb078AlphaDummy420 g) from
                                (by
                                  unfold nb078AlphaDummy420;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0419 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy410))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy412 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy417) ≠ (nb078AlphaDummy424) from (by
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
                  (nb078_support_mem_0423 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy417) ≠ (nb078AlphaDummy421)
        from (by
          unfold nb078AlphaDummy421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0420)
                  0)))) (show (nb078AlphaDummy419 g) ≠ (nb078AlphaDummy422 g) from (by
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
        ((nb078AlphaDummy410), (nb078AlphaDummy412 g)), ((nb078AlphaDummy409),
        (nb078AlphaDummy411 g)), ((nb078AlphaDummy415), (nb078AlphaDummy416 g)),
        ((nb078AlphaDummy413), (nb078AlphaDummy414 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
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
        ((nb078AlphaDummy410), (nb078AlphaDummy412 g)), ((nb078AlphaDummy409),
        (nb078AlphaDummy411 g)), ((nb078AlphaDummy415), (nb078AlphaDummy416 g)),
        ((nb078AlphaDummy413), (nb078AlphaDummy414 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
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
                                        (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from
                                        (by
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
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0421 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy421), (nb078AlphaDummy422 g)),
                                      ((nb078AlphaDummy417), (nb078AlphaDummy419 g)),
                                      ((nb078AlphaDummy418), (nb078AlphaDummy420 g)),
                                      ((nb078AlphaDummy410), (nb078AlphaDummy412 g)),
                                      ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
                                      ((nb078AlphaDummy415), (nb078AlphaDummy416 g)),
                                      ((nb078AlphaDummy413), (nb078AlphaDummy414 g)),
                                      ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                      ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                      ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
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
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from
                                        (by
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
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0421 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy421), (nb078AlphaDummy422 g)),
                                      ((nb078AlphaDummy417), (nb078AlphaDummy419 g)),
                                      ((nb078AlphaDummy418), (nb078AlphaDummy420 g)),
                                      ((nb078AlphaDummy410), (nb078AlphaDummy412 g)),
                                      ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
                                      ((nb078AlphaDummy415), (nb078AlphaDummy416 g)),
                                      ((nb078AlphaDummy413), (nb078AlphaDummy414 g)),
                                      ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                      ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                      ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
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

/-! Certificates from `NAR4C078C001Part124`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0100`. -/
@[expose]
noncomputable def nb078SplitAlpha0100 (x : Var) (y : Var) (g : Var) :
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
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
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
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy571),
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
                              ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                              ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                              ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                              ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                              ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0101`. -/
@[expose]
noncomputable def nb078SplitAlpha0101 (x : Var) (y : Var) (g : Var) (dv_g_x : g ≠ x)
    (dv_g_y : g ≠ y) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (synWf (Class.cv (nb078AlphaDummy001)) (Class.cv (nb078AlphaDummy004))
          (Class.cv (nb078AlphaDummy003)))
        (Wff.neg (synWfun (synCcnv (Class.cv (nb078AlphaDummy001))))))
      (Wff.imp (synWf (Class.cv g) (Class.cv y) (Class.cv x))
        (Wff.neg (synWfun (synCcnv (Class.cv g))))) :=
  (TAlphaWff.imp (TAlphaWff.conj (TAlphaWff.neg (nb078SplitAlpha0057 x y g dv_g_y))
      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
                                    ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
                                    ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)),
                                    ((nb078AlphaDummy521), (nb078AlphaDummy522 x g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0058 x y g))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy530) from (by
          unfold
            nb078AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0568)
                  1)))) (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy532 g) from (by
          unfold
            nb078AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0570
                    g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy529)
        from (by
          unfold
            nb078AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0568)
                  0)))) (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy531 g) from (by
          unfold
            nb078AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0570
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy559)
        from (by
          unfold
            nb078AlphaDummy559;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0572)
                  0)))) (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy560 g) from (by
          unfold
            nb078AlphaDummy560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0573
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy533)
        from (by
          unfold
            nb078AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0569)
                  0)))) (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy534 g) from (by
          unfold
            nb078AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0571
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy001))).fv ∪ ((synCvv)).fv) (by decide)) (freshVar_injective
        (((Class.cv g)).fv ∪ ((synCvv)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy526))).fv ∪ ((Class.cv (nb078AlphaDummy525))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy528 g))).fv ∪ ((Class.cv
        (nb078AlphaDummy527 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb078SplitAlpha0059 x y g))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy530) from (by
          unfold
            nb078AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0568)
                  1)))) (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy532 g) from (by
          unfold
            nb078AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0570
                    g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy529)
        from (by
          unfold
            nb078AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0568)
                  0)))) (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy531 g) from (by
          unfold
            nb078AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0570
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy559)
        from (by
          unfold
            nb078AlphaDummy559;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0572)
                  0)))) (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy560 g) from (by
          unfold
            nb078AlphaDummy560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0573
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy533)
        from (by
          unfold
            nb078AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0569)
                  0)))) (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy534 g) from (by
          unfold
            nb078AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0571
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy001))).fv ∪ ((synCvv)).fv) (by decide)) (freshVar_injective
        (((Class.cv g)).fv ∪ ((synCvv)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy526))).fv ∪ ((Class.cv (nb078AlphaDummy525))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy528 g))).fv ∪ ((Class.cv
        (nb078AlphaDummy527 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb078SplitAlpha0059 x y g)))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy001) ≠ (nb078AlphaDummy526) from (by
                                        unfold nb078AlphaDummy526;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0582)
                                                1)))) (show g ≠ (nb078AlphaDummy528 g) from
                                      (by
                                        unfold nb078AlphaDummy528;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0583 g)
                                                1)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy001) ≠ (nb078AlphaDummy525) from
                                        (by
                                          unfold nb078AlphaDummy525;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0582)
                                                  0)))) (show g ≠ (nb078AlphaDummy527 g) from
                                        (by
                                          unfold nb078AlphaDummy527;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0583 g) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy001) ≠
        (nb078AlphaDummy523) from (by
          unfold nb078AlphaDummy523;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0580) 0)))) (show g ≠ (nb078AlphaDummy524 x g) from (by
          unfold nb078AlphaDummy524;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0581 x g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy001) ≠ (nb078AlphaDummy521) from (by
          unfold nb078AlphaDummy521;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0578) 0)))) (show g ≠ (nb078AlphaDummy522 x g) from (by
          unfold nb078AlphaDummy522;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0579 x g) 0)))) (TAlphaVar.here _ _ _)))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy003) ≠ (nb078AlphaDummy523) from (by
                                unfold nb078AlphaDummy523;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0586) 0))))
                            (show x ≠ (nb078AlphaDummy524 x g) from (by
                                unfold nb078AlphaDummy524;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0587 x g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy003) ≠ (nb078AlphaDummy521) from (by
                                  unfold nb078AlphaDummy521;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0584) 0))))
                              (show x ≠ (nb078AlphaDummy522 x g) from (by
                                  unfold nb078AlphaDummy522;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0585 x g)
                                          0)))) (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide))
                                (Ne.symm dv_g_x) (TAlphaVar.there
                                  (freshVar_injective ((∅ : Finset Var)) (by decide))
                                  dv_x_y (TAlphaVar.here _ _ _)))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
                                    ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
                                    ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)),
                                    ((nb078AlphaDummy521), (nb078AlphaDummy522 x g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0058 x y g))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy530) from (by
          unfold
            nb078AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0568)
                  1)))) (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy532 g) from (by
          unfold
            nb078AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0570
                    g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy529)
        from (by
          unfold
            nb078AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0568)
                  0)))) (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy531 g) from (by
          unfold
            nb078AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0570
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy559)
        from (by
          unfold
            nb078AlphaDummy559;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0572)
                  0)))) (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy560 g) from (by
          unfold
            nb078AlphaDummy560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0573
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy533)
        from (by
          unfold
            nb078AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0569)
                  0)))) (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy534 g) from (by
          unfold
            nb078AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0571
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy001))).fv ∪ ((synCvv)).fv) (by decide)) (freshVar_injective
        (((Class.cv g)).fv ∪ ((synCvv)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy526))).fv ∪ ((Class.cv (nb078AlphaDummy525))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy528 g))).fv ∪ ((Class.cv
        (nb078AlphaDummy527 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb078SplitAlpha0059 x y g))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy530) from (by
          unfold
            nb078AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0568)
                  1)))) (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy532 g) from (by
          unfold
            nb078AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0570
                    g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy529)
        from (by
          unfold
            nb078AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0568)
                  0)))) (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy531 g) from (by
          unfold
            nb078AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0570
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy559)
        from (by
          unfold
            nb078AlphaDummy559;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0572)
                  0)))) (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy560 g) from (by
          unfold
            nb078AlphaDummy560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0573
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy533)
        from (by
          unfold
            nb078AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0569)
                  0)))) (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy534 g) from (by
          unfold
            nb078AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0571
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy001))).fv ∪ ((synCvv)).fv) (by decide)) (freshVar_injective
        (((Class.cv g)).fv ∪ ((synCvv)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy526))).fv ∪ ((Class.cv (nb078AlphaDummy525))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy528 g))).fv ∪ ((Class.cv
        (nb078AlphaDummy527 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb078SplitAlpha0059 x y g)))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy001) ≠ (nb078AlphaDummy526) from (by
                                        unfold nb078AlphaDummy526;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0582)
                                                1)))) (show g ≠ (nb078AlphaDummy528 g) from
                                      (by
                                        unfold nb078AlphaDummy528;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0583 g)
                                                1)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy001) ≠ (nb078AlphaDummy525) from
                                        (by
                                          unfold nb078AlphaDummy525;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0582)
                                                  0)))) (show g ≠ (nb078AlphaDummy527 g) from
                                        (by
                                          unfold nb078AlphaDummy527;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0583 g) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy001) ≠
        (nb078AlphaDummy523) from (by
          unfold nb078AlphaDummy523;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0580) 0)))) (show g ≠ (nb078AlphaDummy524 x g) from (by
          unfold nb078AlphaDummy524;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0581 x g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy001) ≠ (nb078AlphaDummy521) from (by
          unfold nb078AlphaDummy521;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0578) 0)))) (show g ≠ (nb078AlphaDummy522 x g) from (by
          unfold nb078AlphaDummy522;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0579 x g) 0)))) (TAlphaVar.here _ _ _)))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy003) ≠ (nb078AlphaDummy523) from (by
                                unfold nb078AlphaDummy523;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0586) 0))))
                            (show x ≠ (nb078AlphaDummy524 x g) from (by
                                unfold nb078AlphaDummy524;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0587 x g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy003) ≠ (nb078AlphaDummy521) from (by
                                  unfold nb078AlphaDummy521;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0584) 0))))
                              (show x ≠ (nb078AlphaDummy522 x g) from (by
                                  unfold nb078AlphaDummy522;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0585 x g)
                                          0)))) (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide))
                                (Ne.symm dv_g_x) (TAlphaVar.there
                                  (freshVar_injective ((∅ : Finset Var)) (by decide))
                                  dv_x_y (TAlphaVar.here _ _ _)))))))))))))) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
                    ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                    ((nb078AlphaDummy003), x)] (synCvv) (by simp only [fv_syn_cvv])))
              (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0061 x y g))))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy526) from (by
                        unfold nb078AlphaDummy526;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0582) 1))))
                    (show g ≠ (nb078AlphaDummy528 g) from (by
                        unfold nb078AlphaDummy528;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0583 g) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy525) from (by
                          unfold nb078AlphaDummy525;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0582) 0))))
                      (show g ≠ (nb078AlphaDummy527 g) from (by
                          unfold nb078AlphaDummy527;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0583 g) 0))))
                      (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                              (TAlphaWff.neg (nb078SplitAlpha0081 x y g))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfReflOn
                          [((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                            ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
                            ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCid) (nb078WppRefl0273 x y g)))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                              (TAlphaWff.neg (nb078SplitAlpha0081 x y g))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfReflOn
                          [((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                            ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
                            ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCid) (nb078WppRefl0273 x y g)))))))))) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there (Ne.symm
                        (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy575) from (by
                            unfold nb078AlphaDummy575;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0590) 0))))) (Ne.symm
                        (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy576 g) from (by
                            unfold nb078AlphaDummy576;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0591 g) 0)))))
                      (TAlphaVar.there (Ne.symm
                          (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy575) from (by
                              unfold nb078AlphaDummy575;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0588) 0))))) (Ne.symm
                          (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy576 g) from (by
                              unfold nb078AlphaDummy576;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0589 g) 0)))))
                        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb078SplitAlpha0082 x y g)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex
                                      (TAlphaWff.neg (nb078SplitAlpha0083 x y g)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb078SplitAlpha0083 x y g))))))))))))) (TAlphaWff.ex
                  (TAlphaWff.conj (nb078SplitAlpha0094 x y g) (TAlphaWff.classMem
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078SplitAlpha0095 x y g)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy728) from (by
          unfold nb078AlphaDummy728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0788)
                  1)))) (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy730 g) from (by
          unfold nb078AlphaDummy730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0790 g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy727)
        from (by
          unfold nb078AlphaDummy727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0788)
                  0)))) (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy729 g) from (by
          unfold nb078AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0790 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy757)
        from (by
          unfold nb078AlphaDummy757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0792)
                  0)))) (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy758 g) from (by
          unfold nb078AlphaDummy758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0793
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy731)
        from (by
          unfold nb078AlphaDummy731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0789)
                  0)))) (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy732 g) from (by
          unfold nb078AlphaDummy732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0791
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (Class.cv
        (nb078AlphaDummy001)))).fv ∪ ((synCcnv (synCcnv (Class.cv
        (nb078AlphaDummy001))))).fv) (by decide)) (freshVar_injective (((synCcnv
        (Class.cv g))).fv ∪ ((synCcnv (synCcnv (Class.cv g)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078AlphaDummy571))).fv ∪ ((Class.cv
        (nb078AlphaDummy570))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy574 g))).fv ∪ ((Class.cv (nb078AlphaDummy573 g))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078SplitAlpha0096 x y g)))))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy728) from (by
          unfold nb078AlphaDummy728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0788)
                  1)))) (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy730 g) from (by
          unfold nb078AlphaDummy730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0790 g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy727)
        from (by
          unfold nb078AlphaDummy727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0788)
                  0)))) (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy729 g) from (by
          unfold nb078AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0790 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy757)
        from (by
          unfold nb078AlphaDummy757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0792)
                  0)))) (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy758 g) from (by
          unfold nb078AlphaDummy758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0793
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy731)
        from (by
          unfold nb078AlphaDummy731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0789)
                  0)))) (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy732 g) from (by
          unfold nb078AlphaDummy732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0791
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (Class.cv
        (nb078AlphaDummy001)))).fv ∪ ((synCcnv (synCcnv (Class.cv
        (nb078AlphaDummy001))))).fv) (by decide)) (freshVar_injective (((synCcnv
        (Class.cv g))).fv ∪ ((synCcnv (synCcnv (Class.cv g)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078AlphaDummy571))).fv ∪ ((Class.cv
        (nb078AlphaDummy570))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy574 g))).fv ∪ ((Class.cv (nb078AlphaDummy573 g))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078SplitAlpha0096 x y g))))))))))))))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                        (nb078AlphaDummy368) ≠ (nb078AlphaDummy371) from
                                        (by
                                          unfold nb078AlphaDummy371;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0372)
                                                  0))))) (Ne.symm (show
                                        (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy372 g)
                                        from (by
                                          unfold nb078AlphaDummy372;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0373 g) 0)))))
                                    (TAlphaVar.there (Ne.symm (show (nb078AlphaDummy367) ≠
        (nb078AlphaDummy371) from (by
          unfold nb078AlphaDummy371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0370) 0))))) (Ne.symm (show (nb078AlphaDummy369 g) ≠
        (nb078AlphaDummy372 g) from (by
          unfold nb078AlphaDummy372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0371 g) 0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0097 x y g))))) (TAlphaWff.classMem
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0098 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy405), (nb078AlphaDummy406 g)), ((nb078AlphaDummy374),
        (nb078AlphaDummy376 g)), ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
        ((nb078AlphaDummy403), (nb078AlphaDummy404 g)), ((nb078AlphaDummy377),
        (nb078AlphaDummy378 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0098 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy405), (nb078AlphaDummy406 g)), ((nb078AlphaDummy374),
        (nb078AlphaDummy376 g)), ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
        ((nb078AlphaDummy403), (nb078AlphaDummy404 g)), ((nb078AlphaDummy377),
        (nb078AlphaDummy378 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y), ((nb078AlphaDummy003),
        x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0099 x y g))))) (TAlphaWff.classMem
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0100 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy441), (nb078AlphaDummy442 g)), ((nb078AlphaDummy410),
        (nb078AlphaDummy412 g)), ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
        ((nb078AlphaDummy439), (nb078AlphaDummy440 g)), ((nb078AlphaDummy413),
        (nb078AlphaDummy414 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0100 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy441), (nb078AlphaDummy442 g)), ((nb078AlphaDummy410),
        (nb078AlphaDummy412 g)), ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
        ((nb078AlphaDummy439), (nb078AlphaDummy440 g)), ((nb078AlphaDummy413),
        (nb078AlphaDummy414 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y), ((nb078AlphaDummy003),
        x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy001) ≠ (nb078AlphaDummy368) from (by
                                        unfold nb078AlphaDummy368;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0460)
                                                1)))) (show g ≠ (nb078AlphaDummy370 g) from
                                      (by
                                        unfold nb078AlphaDummy370;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0461 g)
                                                1)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy001) ≠ (nb078AlphaDummy367) from
                                        (by
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
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0461 g) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy001) ≠
        (nb078AlphaDummy371) from (by
          unfold nb078AlphaDummy371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0458) 0)))) (show g ≠ (nb078AlphaDummy372 g) from (by
          unfold nb078AlphaDummy372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0459 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy001) ≠ (nb078AlphaDummy571) from (by
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
                  (nb078_support_mem_0755 g)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
