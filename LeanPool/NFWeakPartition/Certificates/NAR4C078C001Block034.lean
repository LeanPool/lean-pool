/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block033

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part105`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0079`. -/
@[expose]
noncomputable def nb078SplitAlpha0079 (x : Var) (y : Var) (g : Var) :
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
        ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
        ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
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
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
        ((nb078AlphaDummy565), (nb078AlphaDummy566 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
        ((nb078AlphaDummy565), (nb078AlphaDummy566 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy417))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy419 g))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                                    ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                                    ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
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
                                    ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                                    ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
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
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
        ((nb078AlphaDummy565), (nb078AlphaDummy566 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
        ((nb078AlphaDummy565), (nb078AlphaDummy566 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy417))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy419
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                                      ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                                      ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
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
                                      ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                                      ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part106`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0080`. -/
@[expose]
noncomputable def nb078SplitAlpha0080 (x : Var) (y : Var) (g : Var) :
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
        ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
        ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
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
                                        ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                                        ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
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
        ((nb078AlphaDummy567), (nb078AlphaDummy568 g)), ((nb078AlphaDummy565),
        (nb078AlphaDummy566 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
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
                            ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                            ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
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
                            ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                            ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
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
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
        ((nb078AlphaDummy565), (nb078AlphaDummy566 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
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
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)), ((nb078AlphaDummy567),
        (nb078AlphaDummy568 g)), ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
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
                              ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                              ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
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
                              ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                              ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
                              ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0081`. -/
@[expose]
noncomputable def nb078SplitAlpha0081 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
        ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classEq (Class.cv (nb078AlphaDummy575))
          (synCop (Class.cv (nb078AlphaDummy569)) (Class.cv (nb078AlphaDummy570))))
        (Wff.neg (synWex (nb078AlphaDummy571) (synWa
              (synWbr (Class.cv (nb078AlphaDummy569))
                (synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))
                (Class.cv (nb078AlphaDummy571))) (synWbr (Class.cv (nb078AlphaDummy571))
                (synCcnv (Class.cv (nb078AlphaDummy001)))
                (Class.cv (nb078AlphaDummy570)))))))
      (Wff.imp (Wff.classEq (Class.cv (nb078AlphaDummy576 g))
          (synCop (Class.cv (nb078AlphaDummy572 g)) (Class.cv (nb078AlphaDummy573 g))))
        (Wff.neg (synWex (nb078AlphaDummy574 g) (synWa
              (synWbr (Class.cv (nb078AlphaDummy572 g))
                (synCcnv (synCcnv (Class.cv g))) (Class.cv (nb078AlphaDummy574 g)))
              (synWbr (Class.cv (nb078AlphaDummy574 g)) (synCcnv (Class.cv g))
                (Class.cv (nb078AlphaDummy573 g))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy575) from (by
                unfold nb078AlphaDummy575;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0590) 0))))) (Ne.symm
            (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy576 g) from (by
                unfold nb078AlphaDummy576;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0591 g) 0)))))
          (TAlphaVar.there (Ne.symm (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy575) from
                (by
                  unfold nb078AlphaDummy575;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0588) 0)))))
            (Ne.symm (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy576 g) from (by
                  unfold nb078AlphaDummy576;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0589 g) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0062 x y g)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy578) from
                                    (by
                                      unfold nb078AlphaDummy578;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0620)
                                              1)))) (show
                                    (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy580 g) from
                                    (by
                                      unfold nb078AlphaDummy580;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0622 g)
                                              1)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy570) ≠ (nb078AlphaDummy577) from (by
                                        unfold nb078AlphaDummy577;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0620)
                                                0)))) (show (nb078AlphaDummy573 g) ≠
                                        (nb078AlphaDummy579 g) from (by
                                        unfold nb078AlphaDummy579;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0622 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy570) ≠ (nb078AlphaDummy607) from
                                        (by
                                          unfold nb078AlphaDummy607;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0624)
                                                  0)))) (show (nb078AlphaDummy573 g) ≠
        (nb078AlphaDummy608 g) from (by
                                          unfold nb078AlphaDummy608;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0625 g) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy570) ≠
        (nb078AlphaDummy581) from (by
          unfold nb078AlphaDummy581;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0621) 0)))) (show (nb078AlphaDummy573 g) ≠
        (nb078AlphaDummy582 g) from (by
          unfold nb078AlphaDummy582;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0623 g) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb078AlphaDummy569))).fv ∪
                                      ((Class.cv (nb078AlphaDummy570))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy572 g))).fv ∪
                                      ((Class.cv (nb078AlphaDummy573 g))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078SplitAlpha0063 x y g)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy578) from
                                    (by
                                      unfold nb078AlphaDummy578;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0620)
                                              1)))) (show
                                    (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy580 g) from
                                    (by
                                      unfold nb078AlphaDummy580;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0622 g)
                                              1)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy570) ≠ (nb078AlphaDummy577) from (by
                                        unfold nb078AlphaDummy577;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0620)
                                                0)))) (show (nb078AlphaDummy573 g) ≠
                                        (nb078AlphaDummy579 g) from (by
                                        unfold nb078AlphaDummy579;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0622 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy570) ≠ (nb078AlphaDummy607) from
                                        (by
                                          unfold nb078AlphaDummy607;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0624)
                                                  0)))) (show (nb078AlphaDummy573 g) ≠
        (nb078AlphaDummy608 g) from (by
                                          unfold nb078AlphaDummy608;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0625 g) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy570) ≠
        (nb078AlphaDummy581) from (by
          unfold nb078AlphaDummy581;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0621) 0)))) (show (nb078AlphaDummy573 g) ≠
        (nb078AlphaDummy582 g) from (by
          unfold nb078AlphaDummy582;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0623 g) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb078AlphaDummy569))).fv ∪
                                      ((Class.cv (nb078AlphaDummy570))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy572 g))).fv ∪
                                      ((Class.cv (nb078AlphaDummy573 g))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078SplitAlpha0063 x y g)))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0064 x y g)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078AlphaDummy571) ≠
        (nb078AlphaDummy614) from (by
          unfold nb078AlphaDummy614;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0658) 1)))) (show (nb078AlphaDummy574 g) ≠
        (nb078AlphaDummy616 g) from (by
          unfold nb078AlphaDummy616;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0660 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy571) ≠ (nb078AlphaDummy613) from (by
          unfold nb078AlphaDummy613;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0658) 0)))) (show (nb078AlphaDummy574 g) ≠
        (nb078AlphaDummy615 g) from (by
          unfold nb078AlphaDummy615;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0660 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy571) ≠ (nb078AlphaDummy643) from (by
          unfold nb078AlphaDummy643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0662) 0)))) (show (nb078AlphaDummy574 g) ≠
        (nb078AlphaDummy644 g) from (by
          unfold nb078AlphaDummy644;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0663 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy571) ≠ (nb078AlphaDummy617) from (by
          unfold nb078AlphaDummy617;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0659) 0)))) (show (nb078AlphaDummy574 g) ≠
        (nb078AlphaDummy618 g) from (by
          unfold nb078AlphaDummy618;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0661 g) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078AlphaDummy569))).fv ∪ ((Class.cv (nb078AlphaDummy571))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy572 g))).fv ∪
        ((Class.cv (nb078AlphaDummy574 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078SplitAlpha0065 x y g)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy645), (nb078AlphaDummy646 g)), ((nb078AlphaDummy614),
        (nb078AlphaDummy616 g)), ((nb078AlphaDummy613), (nb078AlphaDummy615 g)),
        ((nb078AlphaDummy643), (nb078AlphaDummy644 g)), ((nb078AlphaDummy617),
        (nb078AlphaDummy618 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy567), (nb078AlphaDummy568 g)), ((nb078AlphaDummy565),
        (nb078AlphaDummy566 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078AlphaDummy571) ≠
        (nb078AlphaDummy614) from (by
          unfold nb078AlphaDummy614;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0658) 1)))) (show (nb078AlphaDummy574 g) ≠
        (nb078AlphaDummy616 g) from (by
          unfold nb078AlphaDummy616;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0660 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy571) ≠ (nb078AlphaDummy613) from (by
          unfold nb078AlphaDummy613;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0658) 0)))) (show (nb078AlphaDummy574 g) ≠
        (nb078AlphaDummy615 g) from (by
          unfold nb078AlphaDummy615;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0660 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy571) ≠ (nb078AlphaDummy643) from (by
          unfold nb078AlphaDummy643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0662) 0)))) (show (nb078AlphaDummy574 g) ≠
        (nb078AlphaDummy644 g) from (by
          unfold nb078AlphaDummy644;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0663 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy571) ≠ (nb078AlphaDummy617) from (by
          unfold nb078AlphaDummy617;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0659) 0)))) (show (nb078AlphaDummy574 g) ≠
        (nb078AlphaDummy618 g) from (by
          unfold nb078AlphaDummy618;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0661 g) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078AlphaDummy569))).fv ∪ ((Class.cv (nb078AlphaDummy571))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy572 g))).fv ∪
        ((Class.cv (nb078AlphaDummy574 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078SplitAlpha0065 x y g)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy645), (nb078AlphaDummy646 g)), ((nb078AlphaDummy614),
        (nb078AlphaDummy616 g)), ((nb078AlphaDummy613), (nb078AlphaDummy615 g)),
        ((nb078AlphaDummy643), (nb078AlphaDummy644 g)), ((nb078AlphaDummy617),
        (nb078AlphaDummy618 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy567), (nb078AlphaDummy568 g)), ((nb078AlphaDummy565),
        (nb078AlphaDummy566 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex
                (TAlphaWff.ex (TAlphaWff.neg (nb078SplitAlpha0074 x y g))))))
          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0075 x y g)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078AlphaDummy570) ≠
        (nb078AlphaDummy728) from (by
          unfold nb078AlphaDummy728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0788) 1)))) (show (nb078AlphaDummy573 g) ≠
        (nb078AlphaDummy730 g) from (by
          unfold nb078AlphaDummy730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0790 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy570) ≠ (nb078AlphaDummy727) from (by
          unfold nb078AlphaDummy727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0788) 0)))) (show (nb078AlphaDummy573 g) ≠
        (nb078AlphaDummy729 g) from (by
          unfold nb078AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0790 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy570) ≠ (nb078AlphaDummy757) from (by
          unfold nb078AlphaDummy757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0792) 0)))) (show (nb078AlphaDummy573 g) ≠
        (nb078AlphaDummy758 g) from (by
          unfold nb078AlphaDummy758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0793 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy570) ≠ (nb078AlphaDummy731) from (by
          unfold nb078AlphaDummy731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0789) 0)))) (show (nb078AlphaDummy573 g) ≠
        (nb078AlphaDummy732 g) from (by
          unfold nb078AlphaDummy732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0791 g) 0)))) (TAlphaVar.there (freshVar_injective
        (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪ ((synCcnv (synCcnv (Class.cv
        (nb078AlphaDummy001))))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv g))).fv ∪ ((synCcnv (synCcnv (Class.cv g)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078AlphaDummy571))).fv ∪ ((Class.cv (nb078AlphaDummy570))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy574 g))).fv ∪
        ((Class.cv (nb078AlphaDummy573 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078SplitAlpha0076 x y g)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy759), (nb078AlphaDummy760 g)), ((nb078AlphaDummy728),
        (nb078AlphaDummy730 g)), ((nb078AlphaDummy727), (nb078AlphaDummy729 g)),
        ((nb078AlphaDummy757), (nb078AlphaDummy758 g)), ((nb078AlphaDummy731),
        (nb078AlphaDummy732 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy567), (nb078AlphaDummy568 g)), ((nb078AlphaDummy565),
        (nb078AlphaDummy566 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078AlphaDummy570) ≠
        (nb078AlphaDummy728) from (by
          unfold nb078AlphaDummy728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0788) 1)))) (show (nb078AlphaDummy573 g) ≠
        (nb078AlphaDummy730 g) from (by
          unfold nb078AlphaDummy730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0790 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy570) ≠ (nb078AlphaDummy727) from (by
          unfold nb078AlphaDummy727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0788) 0)))) (show (nb078AlphaDummy573 g) ≠
        (nb078AlphaDummy729 g) from (by
          unfold nb078AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0790 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy570) ≠ (nb078AlphaDummy757) from (by
          unfold nb078AlphaDummy757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0792) 0)))) (show (nb078AlphaDummy573 g) ≠
        (nb078AlphaDummy758 g) from (by
          unfold nb078AlphaDummy758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0793 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy570) ≠ (nb078AlphaDummy731) from (by
          unfold nb078AlphaDummy731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0789) 0)))) (show (nb078AlphaDummy573 g) ≠
        (nb078AlphaDummy732 g) from (by
          unfold nb078AlphaDummy732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0791 g) 0)))) (TAlphaVar.there (freshVar_injective
        (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪ ((synCcnv (synCcnv (Class.cv
        (nb078AlphaDummy001))))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv g))).fv ∪ ((synCcnv (synCcnv (Class.cv g)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078AlphaDummy571))).fv ∪ ((Class.cv (nb078AlphaDummy570))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy574 g))).fv ∪
        ((Class.cv (nb078AlphaDummy573 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078SplitAlpha0076 x y g)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy759), (nb078AlphaDummy760 g)), ((nb078AlphaDummy728),
        (nb078AlphaDummy730 g)), ((nb078AlphaDummy727), (nb078AlphaDummy729 g)),
        ((nb078AlphaDummy757), (nb078AlphaDummy758 g)), ((nb078AlphaDummy731),
        (nb078AlphaDummy732 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy567), (nb078AlphaDummy568 g)), ((nb078AlphaDummy565),
        (nb078AlphaDummy566 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
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
                                  (TAlphaWff.neg (nb078SplitAlpha0077 x y g)))))
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0078 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy405), (nb078AlphaDummy406 g)), ((nb078AlphaDummy374),
        (nb078AlphaDummy376 g)), ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
        ((nb078AlphaDummy403), (nb078AlphaDummy404 g)), ((nb078AlphaDummy377),
        (nb078AlphaDummy378 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy567), (nb078AlphaDummy568 g)), ((nb078AlphaDummy565),
        (nb078AlphaDummy566 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0078 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy405), (nb078AlphaDummy406 g)), ((nb078AlphaDummy374),
        (nb078AlphaDummy376 g)), ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
        ((nb078AlphaDummy403), (nb078AlphaDummy404 g)), ((nb078AlphaDummy377),
        (nb078AlphaDummy378 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy567), (nb078AlphaDummy568 g)), ((nb078AlphaDummy565),
        (nb078AlphaDummy566 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078SplitAlpha0079 x y g)))))
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0080 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy441), (nb078AlphaDummy442 g)), ((nb078AlphaDummy410),
        (nb078AlphaDummy412 g)), ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
        ((nb078AlphaDummy439), (nb078AlphaDummy440 g)), ((nb078AlphaDummy413),
        (nb078AlphaDummy414 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy567), (nb078AlphaDummy568 g)), ((nb078AlphaDummy565),
        (nb078AlphaDummy566 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0080 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy441), (nb078AlphaDummy442 g)), ((nb078AlphaDummy410),
        (nb078AlphaDummy412 g)), ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
        ((nb078AlphaDummy439), (nb078AlphaDummy440 g)), ((nb078AlphaDummy413),
        (nb078AlphaDummy414 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy567), (nb078AlphaDummy568 g)), ((nb078AlphaDummy565),
        (nb078AlphaDummy566 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
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
                                (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy571) from (by
                                    unfold nb078AlphaDummy571;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0752) 2))))
                                (show g ≠ (nb078AlphaDummy574 g) from (by
                                    unfold nb078AlphaDummy574;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0754 g)
                                            2)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy570) from
                                    (by
                                      unfold nb078AlphaDummy570;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0752)
                                              1)))) (show g ≠ (nb078AlphaDummy573 g) from (by
                                      unfold nb078AlphaDummy573;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0754 g)
                                              1)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy001) ≠ (nb078AlphaDummy569) from (by
                                        unfold nb078AlphaDummy569;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0752)
                                                0)))) (show g ≠ (nb078AlphaDummy572 g) from
                                      (by
                                        unfold nb078AlphaDummy572;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0754 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy001) ≠ (nb078AlphaDummy575) from
                                        (by
                                          unfold nb078AlphaDummy575;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0753)
                                                  0)))) (show g ≠ (nb078AlphaDummy576 g) from
                                        (by
                                          unfold nb078AlphaDummy576;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0755 g) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy001) ≠
        (nb078AlphaDummy567) from (by
          unfold nb078AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0750) 0)))) (show g ≠ (nb078AlphaDummy568 g) from (by
          unfold nb078AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0751 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy001) ≠ (nb078AlphaDummy565) from (by
          unfold nb078AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0748) 0)))) (show g ≠ (nb078AlphaDummy566 g) from (by
          unfold nb078AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0749 g) 0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))

theorem nb078_wpp_notmem_1930 : (nb078AlphaDummy567) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy567, fv_syn_cid] using (nb078_compact_fv_empty_0454)

theorem nb078_wpp_notmem_1931 (g : Var) : (nb078AlphaDummy568 g) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy568, fv_syn_cid] using (nb078_compact_fv_empty_0455 g)

theorem nb078_wpp_notmem_1932 : (nb078AlphaDummy565) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy565, fv_syn_cid] using (nb078_compact_fv_empty_0456)

theorem nb078_wpp_notmem_1933 (g : Var) : (nb078AlphaDummy566 g) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy566, fv_syn_cid] using (nb078_compact_fv_empty_0457 g)

theorem nb078_compact_envfresh_0273 (x : Var) (y : Var) (g : Var) :
    TEnvFresh
      [((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
        ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      ((synCid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb078AlphaDummy567) (nb078AlphaDummy568 g)
      (nb078_wpp_notmem_1930) (nb078_wpp_notmem_1931 g)
      (TEnvFresh.consFresh (nb078AlphaDummy565) (nb078AlphaDummy566 g)
        (nb078_wpp_notmem_1932) (nb078_wpp_notmem_1933 g)
        (TEnvFresh.consFresh (nb078AlphaDummy001) g (nb078_wpp_notmem_1220)
          (nb078_wpp_notmem_1221 g)
          (TEnvFresh.consFresh (nb078AlphaDummy004) y (nb078_wpp_notmem_0512)
            (nb078_wpp_notmem_0513 y)
            (TEnvFresh.consFresh (nb078AlphaDummy003) x (nb078_wpp_notmem_0514)
              (nb078_wpp_notmem_0515 x) (TEnvFresh.nil ((synCid)).fv))))))

/-- Checked nominal proof certificate identified upstream as `nb078_wpp_refl_0273`. -/
@[expose]
noncomputable def nb078WppRefl0273 (x : Var) (y : Var) (g : Var) :
    TReflOn
      [((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
        ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      ((synCid)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0273 x y g)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
