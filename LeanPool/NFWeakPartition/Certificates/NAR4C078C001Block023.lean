/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block022

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part076`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0047`. -/
@[expose]
noncomputable def nb078SplitAlpha0047 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy415), (nb078AlphaDummy416 g)),
        ((nb078AlphaDummy413), (nb078AlphaDummy414 g)),
        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
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
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy289),
        (nb078AlphaDummy292 g)), ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)), ((nb078AlphaDummy293),
        (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
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
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy289),
        (nb078AlphaDummy292 g)), ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)), ((nb078AlphaDummy293),
        (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
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
                                    ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                    ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                    ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                    ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
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
                                    ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                    ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                    ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                    ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
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
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy289),
        (nb078AlphaDummy292 g)), ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)), ((nb078AlphaDummy293),
        (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
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
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy289),
        (nb078AlphaDummy292 g)), ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)), ((nb078AlphaDummy293),
        (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
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
                                      ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                      ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                      ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                      ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
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
                                      ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                      ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                      ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                      ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part077`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0048`. -/
@[expose]
noncomputable def nb078SplitAlpha0048 (x : Var) (y : Var) (g : Var) :
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
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
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
                                        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
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
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)), ((nb078AlphaDummy287),
        (nb078AlphaDummy290 g)), ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
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
                            ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                            ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                            ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                            ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
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
                            ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                            ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                            ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                            ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
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
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy289),
        (nb078AlphaDummy292 g)), ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)), ((nb078AlphaDummy293),
        (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
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
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)), ((nb078AlphaDummy288),
        (nb078AlphaDummy291 g)), ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g),
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
                              ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                              ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                              ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                              ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
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
                              ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                              ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                              ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                              ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                              ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part078`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0049`. -/
@[expose]
noncomputable def nb078SplitAlpha0049 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy451), (nb078AlphaDummy452 g)),
        ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy451))
          (Class.cab (nb078AlphaDummy445)
            (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy289))
              (Wff.classEq (Class.cv (nb078AlphaDummy445))
                (synCphi (Class.cv (nb078AlphaDummy446))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy451)) (Class.cab (nb078AlphaDummy445)
              (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy289))
                (Wff.classEq (Class.cv (nb078AlphaDummy445))
                  (synCphi (Class.cv (nb078AlphaDummy446)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy452 g))
          (Class.cab (nb078AlphaDummy447 g)
            (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy292 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                (synCphi (Class.cv (nb078AlphaDummy448 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy452 g))
            (Class.cab (nb078AlphaDummy447 g)
              (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy292 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                  (synCphi (Class.cv (nb078AlphaDummy448 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy446) from
                    (by
                      unfold nb078AlphaDummy446;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0462) 1))))
                  (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy448 g) from (by
                      unfold nb078AlphaDummy448;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0464 g) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy445) from
                      (by
                        unfold nb078AlphaDummy445;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0462) 0))))
                    (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy447 g) from (by
                        unfold nb078AlphaDummy447;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0464 g) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy451) from (by
                          unfold nb078AlphaDummy451;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0466) 0))))
                      (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy452 g) from (by
                          unfold nb078AlphaDummy452;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0467 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy449) from (by
                            unfold nb078AlphaDummy449;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0463) 0))))
                        (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy450 g) from (by
                            unfold nb078AlphaDummy450;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0465 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy289))).fv ∪
                      ((Class.cv (nb078AlphaDummy288))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy292 g))).fv ∪
                      ((Class.cv (nb078AlphaDummy291 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy446))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy448 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy453) ≠ (nb078AlphaDummy460) from (by
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
                  (nb078_support_mem_0471 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy461), (nb078AlphaDummy464 g)), ((nb078AlphaDummy460),
        (nb078AlphaDummy463 g)), ((nb078AlphaDummy459), (nb078AlphaDummy462 g)),
        ((nb078AlphaDummy457), (nb078AlphaDummy458 g)), ((nb078AlphaDummy453),
        (nb078AlphaDummy455 g)), ((nb078AlphaDummy454), (nb078AlphaDummy456 g)),
        ((nb078AlphaDummy446), (nb078AlphaDummy448 g)), ((nb078AlphaDummy445),
        (nb078AlphaDummy447 g)), ((nb078AlphaDummy451), (nb078AlphaDummy452 g)),
        ((nb078AlphaDummy449), (nb078AlphaDummy450 g)), ((nb078AlphaDummy289),
        (nb078AlphaDummy292 g)), ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)), ((nb078AlphaDummy293),
        (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
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
        ((nb078AlphaDummy446), (nb078AlphaDummy448 g)), ((nb078AlphaDummy445),
        (nb078AlphaDummy447 g)), ((nb078AlphaDummy451), (nb078AlphaDummy452 g)),
        ((nb078AlphaDummy449), (nb078AlphaDummy450 g)), ((nb078AlphaDummy289),
        (nb078AlphaDummy292 g)), ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)), ((nb078AlphaDummy293),
        (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy453))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy455
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy453) ≠ (nb078AlphaDummy457) from (by
                                        unfold nb078AlphaDummy457;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0470)
                                                0)))) (show (nb078AlphaDummy455 g) ≠
                                        (nb078AlphaDummy458 g) from (by
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
                                    ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
                                    ((nb078AlphaDummy445), (nb078AlphaDummy447 g)),
                                    ((nb078AlphaDummy451), (nb078AlphaDummy452 g)),
                                    ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
                                    ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                    ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                    ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                    ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
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
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy453) ≠ (nb078AlphaDummy457) from (by
                                        unfold nb078AlphaDummy457;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0470)
                                                0)))) (show (nb078AlphaDummy455 g) ≠
                                        (nb078AlphaDummy458 g) from (by
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
                                    ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
                                    ((nb078AlphaDummy445), (nb078AlphaDummy447 g)),
                                    ((nb078AlphaDummy451), (nb078AlphaDummy452 g)),
                                    ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
                                    ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                    ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                    ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                    ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy446) from
                      (by
                        unfold nb078AlphaDummy446;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0462) 1))))
                    (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy448 g) from (by
                        unfold nb078AlphaDummy448;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0464 g) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy445) from (by
                          unfold nb078AlphaDummy445;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0462) 0))))
                      (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy447 g) from (by
                          unfold nb078AlphaDummy447;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0464 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy451) from (by
                            unfold nb078AlphaDummy451;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0466) 0))))
                        (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy452 g) from (by
                            unfold nb078AlphaDummy452;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0467 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy289) ≠ (nb078AlphaDummy449) from (by
                              unfold nb078AlphaDummy449;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0463) 0))))
                          (show (nb078AlphaDummy292 g) ≠ (nb078AlphaDummy450 g) from (by
                              unfold nb078AlphaDummy450;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0465 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy289))).fv ∪
                        ((Class.cv (nb078AlphaDummy288))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy292 g))).fv ∪
                        ((Class.cv (nb078AlphaDummy291 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
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
                              (show (nb078AlphaDummy448 g) ≠ (nb078AlphaDummy456 g) from
                                (by
                                  unfold nb078AlphaDummy456;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0469 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy446))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy448 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy453) ≠ (nb078AlphaDummy460) from (by
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
                  (nb078_support_mem_0473 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy453) ≠ (nb078AlphaDummy457)
        from (by
          unfold nb078AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0470)
                  0)))) (show (nb078AlphaDummy455 g) ≠ (nb078AlphaDummy458 g) from (by
          unfold nb078AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0471 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy461), (nb078AlphaDummy464 g)), ((nb078AlphaDummy460),
        (nb078AlphaDummy463 g)), ((nb078AlphaDummy459), (nb078AlphaDummy462 g)),
        ((nb078AlphaDummy457), (nb078AlphaDummy458 g)), ((nb078AlphaDummy453),
        (nb078AlphaDummy455 g)), ((nb078AlphaDummy454), (nb078AlphaDummy456 g)),
        ((nb078AlphaDummy446), (nb078AlphaDummy448 g)), ((nb078AlphaDummy445),
        (nb078AlphaDummy447 g)), ((nb078AlphaDummy451), (nb078AlphaDummy452 g)),
        ((nb078AlphaDummy449), (nb078AlphaDummy450 g)), ((nb078AlphaDummy289),
        (nb078AlphaDummy292 g)), ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)), ((nb078AlphaDummy293),
        (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
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
        ((nb078AlphaDummy446), (nb078AlphaDummy448 g)), ((nb078AlphaDummy445),
        (nb078AlphaDummy447 g)), ((nb078AlphaDummy451), (nb078AlphaDummy452 g)),
        ((nb078AlphaDummy449), (nb078AlphaDummy450 g)), ((nb078AlphaDummy289),
        (nb078AlphaDummy292 g)), ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)), ((nb078AlphaDummy293),
        (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy453))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy455
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy453) ≠ (nb078AlphaDummy457) from
                                        (by
                                          unfold nb078AlphaDummy457;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0470)
                                                  0)))) (show (nb078AlphaDummy455 g) ≠
        (nb078AlphaDummy458 g) from (by
                                          unfold nb078AlphaDummy458;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0471 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy457), (nb078AlphaDummy458 g)),
                                      ((nb078AlphaDummy453), (nb078AlphaDummy455 g)),
                                      ((nb078AlphaDummy454), (nb078AlphaDummy456 g)),
                                      ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
                                      ((nb078AlphaDummy445), (nb078AlphaDummy447 g)),
                                      ((nb078AlphaDummy451), (nb078AlphaDummy452 g)),
                                      ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
                                      ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                      ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                      ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                      ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy453) ≠ (nb078AlphaDummy457) from (by
                                        unfold nb078AlphaDummy457;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0470)
                                                0)))) (show (nb078AlphaDummy455 g) ≠
                                        (nb078AlphaDummy458 g) from (by
                                        unfold nb078AlphaDummy458;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0471 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy453) ≠ (nb078AlphaDummy457) from
                                        (by
                                          unfold nb078AlphaDummy457;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0470)
                                                  0)))) (show (nb078AlphaDummy455 g) ≠
        (nb078AlphaDummy458 g) from (by
                                          unfold nb078AlphaDummy458;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0471 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy457), (nb078AlphaDummy458 g)),
                                      ((nb078AlphaDummy453), (nb078AlphaDummy455 g)),
                                      ((nb078AlphaDummy454), (nb078AlphaDummy456 g)),
                                      ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
                                      ((nb078AlphaDummy445), (nb078AlphaDummy447 g)),
                                      ((nb078AlphaDummy451), (nb078AlphaDummy452 g)),
                                      ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
                                      ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                      ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                      ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                      ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
