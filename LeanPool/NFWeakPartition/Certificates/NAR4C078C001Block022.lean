/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block021

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part073`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0044`. -/
@[expose]
noncomputable def nb078SplitAlpha0044 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy363), (nb078AlphaDummy364 g)),
        ((nb078AlphaDummy332), (nb078AlphaDummy334 g)),
        ((nb078AlphaDummy331), (nb078AlphaDummy333 g)),
        ((nb078AlphaDummy361), (nb078AlphaDummy362 g)),
        ((nb078AlphaDummy335), (nb078AlphaDummy336 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb078AlphaDummy363))
            (synCcompl (synCphi (Class.cv (nb078AlphaDummy332)))))
          (Wff.classMem (Class.cv (nb078AlphaDummy363)) (synCcompl (synCsn (synC0c))))))
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb078AlphaDummy364 g))
            (synCcompl (synCphi (Class.cv (nb078AlphaDummy334 g)))))
          (Wff.classMem (Class.cv (nb078AlphaDummy364 g))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy332) ≠ (nb078AlphaDummy339) from (by
                                unfold nb078AlphaDummy339;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0338) 0))))
                            (show (nb078AlphaDummy334 g) ≠ (nb078AlphaDummy341 g) from (by
                                unfold nb078AlphaDummy341;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0339 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy332) ≠ (nb078AlphaDummy340) from (by
                                  unfold nb078AlphaDummy340;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0338) 1))))
                              (show (nb078AlphaDummy334 g) ≠ (nb078AlphaDummy342 g) from
                                (by
                                  unfold nb078AlphaDummy342;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0339 g) 1))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy332) ≠ (nb078AlphaDummy365) from (by
                                    unfold nb078AlphaDummy365;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0368) 0)))) (show
                                  (nb078AlphaDummy334 g) ≠ (nb078AlphaDummy366 g) from (by
                                    unfold nb078AlphaDummy366;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0369 g)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy332) ≠ (nb078AlphaDummy363) from
                                    (by
                                      unfold nb078AlphaDummy363;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0366)
                                              0)))) (show
                                    (nb078AlphaDummy334 g) ≠ (nb078AlphaDummy364 g) from
                                    (by
                                      unfold nb078AlphaDummy364;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0367 g)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy332))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy334 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy339) ≠ (nb078AlphaDummy346) from (by
          unfold nb078AlphaDummy346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0342) 1)))) (show (nb078AlphaDummy341 g) ≠
        (nb078AlphaDummy349 g) from (by
          unfold nb078AlphaDummy349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0343 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy339) ≠ (nb078AlphaDummy345) from (by
          unfold nb078AlphaDummy345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0342) 0)))) (show (nb078AlphaDummy341 g) ≠
        (nb078AlphaDummy348 g) from (by
          unfold nb078AlphaDummy348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0343 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy339) ≠ (nb078AlphaDummy343)
        from (by
          unfold nb078AlphaDummy343;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0340)
                  0)))) (show (nb078AlphaDummy341 g) ≠ (nb078AlphaDummy344 g) from (by
          unfold nb078AlphaDummy344;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0341 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy347), (nb078AlphaDummy350 g)), ((nb078AlphaDummy346),
        (nb078AlphaDummy349 g)), ((nb078AlphaDummy345), (nb078AlphaDummy348 g)),
        ((nb078AlphaDummy343), (nb078AlphaDummy344 g)), ((nb078AlphaDummy339),
        (nb078AlphaDummy341 g)), ((nb078AlphaDummy340), (nb078AlphaDummy342 g)),
        ((nb078AlphaDummy365), (nb078AlphaDummy366 g)), ((nb078AlphaDummy363),
        (nb078AlphaDummy364 g)), ((nb078AlphaDummy332), (nb078AlphaDummy334 g)),
        ((nb078AlphaDummy331), (nb078AlphaDummy333 g)), ((nb078AlphaDummy361),
        (nb078AlphaDummy362 g)), ((nb078AlphaDummy335), (nb078AlphaDummy336 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)), ((nb078AlphaDummy288),
        (nb078AlphaDummy291 g)), ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy353) from (by
          unfold
            nb078AlphaDummy353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0346)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy354 g) from (by
          unfold
            nb078AlphaDummy354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0347
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy351)
        from (by
          unfold
            nb078AlphaDummy351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0344)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy352 g) from (by
          unfold
            nb078AlphaDummy352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0345
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy353)
        from (by
          unfold
            nb078AlphaDummy353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0350)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy354 g) from (by
          unfold
            nb078AlphaDummy354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0351
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy351)
        from (by
          unfold
            nb078AlphaDummy351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0348)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy352 g) from (by
          unfold
            nb078AlphaDummy352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0349
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy353) from (by
          unfold
            nb078AlphaDummy353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0346)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy354 g) from (by
          unfold
            nb078AlphaDummy354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0347
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy351)
        from (by
          unfold
            nb078AlphaDummy351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0344)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy352 g) from (by
          unfold
            nb078AlphaDummy352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0345
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy353)
        from (by
          unfold
            nb078AlphaDummy353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0350)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy354 g) from (by
          unfold
            nb078AlphaDummy354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0351
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy351)
        from (by
          unfold
            nb078AlphaDummy351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0348)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy352 g) from (by
          unfold
            nb078AlphaDummy352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0349
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy347), (nb078AlphaDummy350 g)), ((nb078AlphaDummy346),
        (nb078AlphaDummy349 g)), ((nb078AlphaDummy345), (nb078AlphaDummy348 g)),
        ((nb078AlphaDummy343), (nb078AlphaDummy344 g)), ((nb078AlphaDummy339),
        (nb078AlphaDummy341 g)), ((nb078AlphaDummy340), (nb078AlphaDummy342 g)),
        ((nb078AlphaDummy365), (nb078AlphaDummy366 g)), ((nb078AlphaDummy363),
        (nb078AlphaDummy364 g)), ((nb078AlphaDummy332), (nb078AlphaDummy334 g)),
        ((nb078AlphaDummy331), (nb078AlphaDummy333 g)), ((nb078AlphaDummy361),
        (nb078AlphaDummy362 g)), ((nb078AlphaDummy335), (nb078AlphaDummy336 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)), ((nb078AlphaDummy288),
        (nb078AlphaDummy291 g)), ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy339))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy341
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy346) ≠
        (nb078AlphaDummy357) from (by
          unfold
            nb078AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0354)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy358 g) from (by
          unfold
            nb078AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0355
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy355)
        from (by
          unfold
            nb078AlphaDummy355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0352)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy356 g) from (by
          unfold
            nb078AlphaDummy356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0353
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy357)
        from (by
          unfold
            nb078AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0354)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy358 g) from (by
          unfold
            nb078AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0355
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy355)
        from (by
          unfold
            nb078AlphaDummy355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0352)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy356 g) from (by
          unfold
            nb078AlphaDummy356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0353
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy359) from (by
          unfold
            nb078AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0358)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy360 g) from (by
          unfold
            nb078AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0359
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy355)
        from (by
          unfold
            nb078AlphaDummy355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0356)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy356 g) from (by
          unfold
            nb078AlphaDummy356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0357
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy347) ≠
        (nb078AlphaDummy359) from (by
          unfold
            nb078AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0358)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy360 g) from (by
          unfold
            nb078AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0359
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy355)
        from (by
          unfold
            nb078AlphaDummy355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0356)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy356 g) from (by
          unfold
            nb078AlphaDummy356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0357
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy339) ≠ (nb078AlphaDummy343) from
                                        (by
                                          unfold nb078AlphaDummy343;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0340)
                                                  0)))) (show (nb078AlphaDummy341 g) ≠
        (nb078AlphaDummy344 g) from (by
                                          unfold nb078AlphaDummy344;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0341 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy343), (nb078AlphaDummy344 g)),
                                      ((nb078AlphaDummy339), (nb078AlphaDummy341 g)),
                                      ((nb078AlphaDummy340), (nb078AlphaDummy342 g)),
                                      ((nb078AlphaDummy365), (nb078AlphaDummy366 g)),
                                      ((nb078AlphaDummy363), (nb078AlphaDummy364 g)),
                                      ((nb078AlphaDummy332), (nb078AlphaDummy334 g)),
                                      ((nb078AlphaDummy331), (nb078AlphaDummy333 g)),
                                      ((nb078AlphaDummy361), (nb078AlphaDummy362 g)),
                                      ((nb078AlphaDummy335), (nb078AlphaDummy336 g)),
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
                                      (nb078AlphaDummy339) ≠ (nb078AlphaDummy343) from (by
                                        unfold nb078AlphaDummy343;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0340)
                                                0)))) (show (nb078AlphaDummy341 g) ≠
                                        (nb078AlphaDummy344 g) from (by
                                        unfold nb078AlphaDummy344;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0341 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy339) ≠ (nb078AlphaDummy343) from
                                        (by
                                          unfold nb078AlphaDummy343;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0340)
                                                  0)))) (show (nb078AlphaDummy341 g) ≠
        (nb078AlphaDummy344 g) from (by
                                          unfold nb078AlphaDummy344;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0341 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy343), (nb078AlphaDummy344 g)),
                                      ((nb078AlphaDummy339), (nb078AlphaDummy341 g)),
                                      ((nb078AlphaDummy340), (nb078AlphaDummy342 g)),
                                      ((nb078AlphaDummy365), (nb078AlphaDummy366 g)),
                                      ((nb078AlphaDummy363), (nb078AlphaDummy364 g)),
                                      ((nb078AlphaDummy332), (nb078AlphaDummy334 g)),
                                      ((nb078AlphaDummy331), (nb078AlphaDummy333 g)),
                                      ((nb078AlphaDummy361), (nb078AlphaDummy362 g)),
                                      ((nb078AlphaDummy335), (nb078AlphaDummy336 g)),
                                      ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                      ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                      ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                      ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy332) ≠ (nb078AlphaDummy339) from (by
                                unfold nb078AlphaDummy339;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0338) 0))))
                            (show (nb078AlphaDummy334 g) ≠ (nb078AlphaDummy341 g) from (by
                                unfold nb078AlphaDummy341;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0339 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy332) ≠ (nb078AlphaDummy340) from (by
                                  unfold nb078AlphaDummy340;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0338) 1))))
                              (show (nb078AlphaDummy334 g) ≠ (nb078AlphaDummy342 g) from
                                (by
                                  unfold nb078AlphaDummy342;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0339 g) 1))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy332) ≠ (nb078AlphaDummy365) from (by
                                    unfold nb078AlphaDummy365;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0368) 0)))) (show
                                  (nb078AlphaDummy334 g) ≠ (nb078AlphaDummy366 g) from (by
                                    unfold nb078AlphaDummy366;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0369 g)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy332) ≠ (nb078AlphaDummy363) from
                                    (by
                                      unfold nb078AlphaDummy363;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0366)
                                              0)))) (show
                                    (nb078AlphaDummy334 g) ≠ (nb078AlphaDummy364 g) from
                                    (by
                                      unfold nb078AlphaDummy364;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0367 g)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy332))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy334 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy339) ≠ (nb078AlphaDummy346) from (by
          unfold nb078AlphaDummy346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0342) 1)))) (show (nb078AlphaDummy341 g) ≠
        (nb078AlphaDummy349 g) from (by
          unfold nb078AlphaDummy349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0343 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy339) ≠ (nb078AlphaDummy345) from (by
          unfold nb078AlphaDummy345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0342) 0)))) (show (nb078AlphaDummy341 g) ≠
        (nb078AlphaDummy348 g) from (by
          unfold nb078AlphaDummy348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0343 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy339) ≠ (nb078AlphaDummy343)
        from (by
          unfold nb078AlphaDummy343;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0340)
                  0)))) (show (nb078AlphaDummy341 g) ≠ (nb078AlphaDummy344 g) from (by
          unfold nb078AlphaDummy344;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0341 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy347), (nb078AlphaDummy350 g)), ((nb078AlphaDummy346),
        (nb078AlphaDummy349 g)), ((nb078AlphaDummy345), (nb078AlphaDummy348 g)),
        ((nb078AlphaDummy343), (nb078AlphaDummy344 g)), ((nb078AlphaDummy339),
        (nb078AlphaDummy341 g)), ((nb078AlphaDummy340), (nb078AlphaDummy342 g)),
        ((nb078AlphaDummy365), (nb078AlphaDummy366 g)), ((nb078AlphaDummy363),
        (nb078AlphaDummy364 g)), ((nb078AlphaDummy332), (nb078AlphaDummy334 g)),
        ((nb078AlphaDummy331), (nb078AlphaDummy333 g)), ((nb078AlphaDummy361),
        (nb078AlphaDummy362 g)), ((nb078AlphaDummy335), (nb078AlphaDummy336 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)), ((nb078AlphaDummy288),
        (nb078AlphaDummy291 g)), ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy353) from (by
          unfold
            nb078AlphaDummy353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0346)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy354 g) from (by
          unfold
            nb078AlphaDummy354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0347
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy351)
        from (by
          unfold
            nb078AlphaDummy351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0344)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy352 g) from (by
          unfold
            nb078AlphaDummy352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0345
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy353)
        from (by
          unfold
            nb078AlphaDummy353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0350)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy354 g) from (by
          unfold
            nb078AlphaDummy354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0351
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy351)
        from (by
          unfold
            nb078AlphaDummy351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0348)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy352 g) from (by
          unfold
            nb078AlphaDummy352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0349
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy353) from (by
          unfold
            nb078AlphaDummy353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0346)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy354 g) from (by
          unfold
            nb078AlphaDummy354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0347
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy351)
        from (by
          unfold
            nb078AlphaDummy351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0344)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy352 g) from (by
          unfold
            nb078AlphaDummy352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0345
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy353)
        from (by
          unfold
            nb078AlphaDummy353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0350)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy354 g) from (by
          unfold
            nb078AlphaDummy354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0351
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy351)
        from (by
          unfold
            nb078AlphaDummy351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0348)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy352 g) from (by
          unfold
            nb078AlphaDummy352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0349
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy347), (nb078AlphaDummy350 g)), ((nb078AlphaDummy346),
        (nb078AlphaDummy349 g)), ((nb078AlphaDummy345), (nb078AlphaDummy348 g)),
        ((nb078AlphaDummy343), (nb078AlphaDummy344 g)), ((nb078AlphaDummy339),
        (nb078AlphaDummy341 g)), ((nb078AlphaDummy340), (nb078AlphaDummy342 g)),
        ((nb078AlphaDummy365), (nb078AlphaDummy366 g)), ((nb078AlphaDummy363),
        (nb078AlphaDummy364 g)), ((nb078AlphaDummy332), (nb078AlphaDummy334 g)),
        ((nb078AlphaDummy331), (nb078AlphaDummy333 g)), ((nb078AlphaDummy361),
        (nb078AlphaDummy362 g)), ((nb078AlphaDummy335), (nb078AlphaDummy336 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)), ((nb078AlphaDummy288),
        (nb078AlphaDummy291 g)), ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy339))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy341
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy346) ≠
        (nb078AlphaDummy357) from (by
          unfold
            nb078AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0354)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy358 g) from (by
          unfold
            nb078AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0355
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy355)
        from (by
          unfold
            nb078AlphaDummy355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0352)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy356 g) from (by
          unfold
            nb078AlphaDummy356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0353
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy357)
        from (by
          unfold
            nb078AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0354)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy358 g) from (by
          unfold
            nb078AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0355
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy355)
        from (by
          unfold
            nb078AlphaDummy355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0352)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy356 g) from (by
          unfold
            nb078AlphaDummy356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0353
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy359) from (by
          unfold
            nb078AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0358)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy360 g) from (by
          unfold
            nb078AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0359
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy355)
        from (by
          unfold
            nb078AlphaDummy355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0356)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy356 g) from (by
          unfold
            nb078AlphaDummy356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0357
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy347) ≠
        (nb078AlphaDummy359) from (by
          unfold
            nb078AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0358)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy360 g) from (by
          unfold
            nb078AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0359
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy355)
        from (by
          unfold
            nb078AlphaDummy355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0356)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy356 g) from (by
          unfold
            nb078AlphaDummy356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0357
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy339) ≠ (nb078AlphaDummy343) from
                                        (by
                                          unfold nb078AlphaDummy343;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0340)
                                                  0)))) (show (nb078AlphaDummy341 g) ≠
        (nb078AlphaDummy344 g) from (by
                                          unfold nb078AlphaDummy344;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0341 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy343), (nb078AlphaDummy344 g)),
                                      ((nb078AlphaDummy339), (nb078AlphaDummy341 g)),
                                      ((nb078AlphaDummy340), (nb078AlphaDummy342 g)),
                                      ((nb078AlphaDummy365), (nb078AlphaDummy366 g)),
                                      ((nb078AlphaDummy363), (nb078AlphaDummy364 g)),
                                      ((nb078AlphaDummy332), (nb078AlphaDummy334 g)),
                                      ((nb078AlphaDummy331), (nb078AlphaDummy333 g)),
                                      ((nb078AlphaDummy361), (nb078AlphaDummy362 g)),
                                      ((nb078AlphaDummy335), (nb078AlphaDummy336 g)),
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
                                      (nb078AlphaDummy339) ≠ (nb078AlphaDummy343) from (by
                                        unfold nb078AlphaDummy343;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0340)
                                                0)))) (show (nb078AlphaDummy341 g) ≠
                                        (nb078AlphaDummy344 g) from (by
                                        unfold nb078AlphaDummy344;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0341 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy339) ≠ (nb078AlphaDummy343) from
                                        (by
                                          unfold nb078AlphaDummy343;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0340)
                                                  0)))) (show (nb078AlphaDummy341 g) ≠
        (nb078AlphaDummy344 g) from (by
                                          unfold nb078AlphaDummy344;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0341 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy343), (nb078AlphaDummy344 g)),
                                      ((nb078AlphaDummy339), (nb078AlphaDummy341 g)),
                                      ((nb078AlphaDummy340), (nb078AlphaDummy342 g)),
                                      ((nb078AlphaDummy365), (nb078AlphaDummy366 g)),
                                      ((nb078AlphaDummy363), (nb078AlphaDummy364 g)),
                                      ((nb078AlphaDummy332), (nb078AlphaDummy334 g)),
                                      ((nb078AlphaDummy331), (nb078AlphaDummy333 g)),
                                      ((nb078AlphaDummy361), (nb078AlphaDummy362 g)),
                                      ((nb078AlphaDummy335), (nb078AlphaDummy336 g)),
                                      ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                      ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                      ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                      ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
          [((nb078AlphaDummy363), (nb078AlphaDummy364 g)),
            ((nb078AlphaDummy332), (nb078AlphaDummy334 g)),
            ((nb078AlphaDummy331), (nb078AlphaDummy333 g)),
            ((nb078AlphaDummy361), (nb078AlphaDummy362 g)),
            ((nb078AlphaDummy335), (nb078AlphaDummy336 g)),
            ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
            ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
            ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
            ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
            ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
            ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part074`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0045`. -/
@[expose]
noncomputable def nb078SplitAlpha0045 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy379))
          (Class.cab (nb078AlphaDummy373)
            (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy367))
              (Wff.classEq (Class.cv (nb078AlphaDummy373))
                (synCphi (Class.cv (nb078AlphaDummy374))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy379)) (Class.cab (nb078AlphaDummy373)
              (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy367))
                (Wff.classEq (Class.cv (nb078AlphaDummy373))
                  (synCphi (Class.cv (nb078AlphaDummy374)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy380 g))
          (Class.cab (nb078AlphaDummy375 g)
            (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy369 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                (synCphi (Class.cv (nb078AlphaDummy376 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy380 g))
            (Class.cab (nb078AlphaDummy375 g)
              (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy369 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                  (synCphi (Class.cv (nb078AlphaDummy376 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy374) from
                    (by
                      unfold nb078AlphaDummy374;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 1))))
                  (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy376 g) from (by
                      unfold nb078AlphaDummy376;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0376 g) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy373) from
                      (by
                        unfold nb078AlphaDummy373;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 0))))
                    (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy375 g) from (by
                        unfold nb078AlphaDummy375;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0376 g) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy379) from (by
                          unfold nb078AlphaDummy379;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0378) 0))))
                      (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy380 g) from (by
                          unfold nb078AlphaDummy380;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0379 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy377) from (by
                            unfold nb078AlphaDummy377;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0375) 0))))
                        (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy378 g) from (by
                            unfold nb078AlphaDummy378;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0377 g) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy001))).fv)
                            (by decide)) (freshVar_injective (((Class.cv g)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy367))).fv ∪
                      ((Class.cv (nb078AlphaDummy368))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy369 g))).fv ∪
                      ((Class.cv (nb078AlphaDummy370 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy381) from (by
                              unfold nb078AlphaDummy381;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0380) 0))))
                          (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy383 g) from (by
                              unfold nb078AlphaDummy383;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0381 g) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy382) from (by
                                unfold nb078AlphaDummy382;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0380) 1))))
                            (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy384 g) from (by
                                unfold nb078AlphaDummy384;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0381 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy374))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy376 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy388) from (by
          unfold nb078AlphaDummy388;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 1)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy391 g) from (by
          unfold nb078AlphaDummy391;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy381) ≠ (nb078AlphaDummy387) from (by
          unfold nb078AlphaDummy387;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy390 g) from (by
          unfold nb078AlphaDummy390;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
          unfold nb078AlphaDummy385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0382) 0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy386 g) from (by
          unfold nb078AlphaDummy386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0383 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy389), (nb078AlphaDummy392 g)), ((nb078AlphaDummy388),
        (nb078AlphaDummy391 g)), ((nb078AlphaDummy387), (nb078AlphaDummy390 g)),
        ((nb078AlphaDummy385), (nb078AlphaDummy386 g)), ((nb078AlphaDummy381),
        (nb078AlphaDummy383 g)), ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
        ((nb078AlphaDummy374), (nb078AlphaDummy376 g)), ((nb078AlphaDummy373),
        (nb078AlphaDummy375 g)), ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy289),
        (nb078AlphaDummy292 g)), ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)), ((nb078AlphaDummy293),
        (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy395) from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy395)
        from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy395) from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy395)
        from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy389), (nb078AlphaDummy392 g)), ((nb078AlphaDummy388),
        (nb078AlphaDummy391 g)), ((nb078AlphaDummy387), (nb078AlphaDummy390 g)),
        ((nb078AlphaDummy385), (nb078AlphaDummy386 g)), ((nb078AlphaDummy381),
        (nb078AlphaDummy383 g)), ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
        ((nb078AlphaDummy374), (nb078AlphaDummy376 g)), ((nb078AlphaDummy373),
        (nb078AlphaDummy375 g)), ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy289),
        (nb078AlphaDummy292 g)), ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)), ((nb078AlphaDummy293),
        (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy381))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy383
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy399) from (by
          unfold
            nb078AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy400 g) from (by
          unfold
            nb078AlphaDummy400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy399)
        from (by
          unfold
            nb078AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy400 g) from (by
          unfold
            nb078AlphaDummy400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy401) from (by
          unfold
            nb078AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy402 g) from (by
          unfold
            nb078AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠
        (nb078AlphaDummy401) from (by
          unfold
            nb078AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy402 g) from (by
          unfold
            nb078AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                                        unfold nb078AlphaDummy385;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0382)
                                                0)))) (show (nb078AlphaDummy383 g) ≠
                                        (nb078AlphaDummy386 g) from (by
                                        unfold nb078AlphaDummy386;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0383 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                                    ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                                    ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                                    ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                                    ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                                    ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
                                    ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
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
                                  (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from
                                    (by
                                      unfold nb078AlphaDummy385;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0382)
                                              0)))) (show
                                    (nb078AlphaDummy383 g) ≠ (nb078AlphaDummy386 g) from
                                    (by
                                      unfold nb078AlphaDummy386;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0383 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                                        unfold nb078AlphaDummy385;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0382)
                                                0)))) (show (nb078AlphaDummy383 g) ≠
                                        (nb078AlphaDummy386 g) from (by
                                        unfold nb078AlphaDummy386;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0383 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                                    ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                                    ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                                    ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                                    ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                                    ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
                                    ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
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
                  (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy374) from
                      (by
                        unfold nb078AlphaDummy374;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 1))))
                    (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy376 g) from (by
                        unfold nb078AlphaDummy376;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0376 g) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy373) from (by
                          unfold nb078AlphaDummy373;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0374) 0))))
                      (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy375 g) from (by
                          unfold nb078AlphaDummy375;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0376 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy379) from (by
                            unfold nb078AlphaDummy379;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0378) 0))))
                        (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy380 g) from (by
                            unfold nb078AlphaDummy380;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0379 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy377) from (by
                              unfold nb078AlphaDummy377;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0375) 0))))
                          (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy378 g) from (by
                              unfold nb078AlphaDummy378;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0377 g) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy001))).fv)
                              (by decide)) (freshVar_injective (((Class.cv g)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy367))).fv ∪
                        ((Class.cv (nb078AlphaDummy368))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy369 g))).fv ∪
                        ((Class.cv (nb078AlphaDummy370 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy381) from (by
                                unfold nb078AlphaDummy381;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0380) 0))))
                            (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy383 g) from (by
                                unfold nb078AlphaDummy383;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0381 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy382) from (by
                                  unfold nb078AlphaDummy382;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0380) 1))))
                              (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy384 g) from
                                (by
                                  unfold nb078AlphaDummy384;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0381 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy374))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy376 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy381) ≠ (nb078AlphaDummy388) from (by
          unfold nb078AlphaDummy388;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 1)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy391 g) from (by
          unfold nb078AlphaDummy391;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy381) ≠ (nb078AlphaDummy387) from (by
          unfold nb078AlphaDummy387;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy390 g) from (by
          unfold nb078AlphaDummy390;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy385)
        from (by
          unfold nb078AlphaDummy385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0382)
                  0)))) (show (nb078AlphaDummy383 g) ≠ (nb078AlphaDummy386 g) from (by
          unfold nb078AlphaDummy386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0383 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy389), (nb078AlphaDummy392 g)), ((nb078AlphaDummy388),
        (nb078AlphaDummy391 g)), ((nb078AlphaDummy387), (nb078AlphaDummy390 g)),
        ((nb078AlphaDummy385), (nb078AlphaDummy386 g)), ((nb078AlphaDummy381),
        (nb078AlphaDummy383 g)), ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
        ((nb078AlphaDummy374), (nb078AlphaDummy376 g)), ((nb078AlphaDummy373),
        (nb078AlphaDummy375 g)), ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy289),
        (nb078AlphaDummy292 g)), ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)), ((nb078AlphaDummy293),
        (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy395) from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy395)
        from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy395) from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy395)
        from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy389), (nb078AlphaDummy392 g)), ((nb078AlphaDummy388),
        (nb078AlphaDummy391 g)), ((nb078AlphaDummy387), (nb078AlphaDummy390 g)),
        ((nb078AlphaDummy385), (nb078AlphaDummy386 g)), ((nb078AlphaDummy381),
        (nb078AlphaDummy383 g)), ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
        ((nb078AlphaDummy374), (nb078AlphaDummy376 g)), ((nb078AlphaDummy373),
        (nb078AlphaDummy375 g)), ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy289),
        (nb078AlphaDummy292 g)), ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)), ((nb078AlphaDummy293),
        (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy381))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy383
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy399) from (by
          unfold
            nb078AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy400 g) from (by
          unfold
            nb078AlphaDummy400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy399)
        from (by
          unfold
            nb078AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy400 g) from (by
          unfold
            nb078AlphaDummy400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy401) from (by
          unfold
            nb078AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy402 g) from (by
          unfold
            nb078AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠
        (nb078AlphaDummy401) from (by
          unfold
            nb078AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy402 g) from (by
          unfold
            nb078AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from
                                        (by
                                          unfold nb078AlphaDummy385;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0382)
                                                  0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy386 g) from (by
                                          unfold nb078AlphaDummy386;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0383 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                                      ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                                      ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                                      ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                                      ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                                      ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
                                      ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
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
                                      (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                                        unfold nb078AlphaDummy385;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0382)
                                                0)))) (show (nb078AlphaDummy383 g) ≠
                                        (nb078AlphaDummy386 g) from (by
                                        unfold nb078AlphaDummy386;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0383 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from
                                        (by
                                          unfold nb078AlphaDummy385;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0382)
                                                  0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy386 g) from (by
                                          unfold nb078AlphaDummy386;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0383 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                                      ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                                      ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                                      ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                                      ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                                      ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
                                      ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
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

/-! Certificates from `NAR4C078C001Part075`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0046`. -/
@[expose]
noncomputable def nb078SplitAlpha0046 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy407), (nb078AlphaDummy408 g)),
        ((nb078AlphaDummy405), (nb078AlphaDummy406 g)),
        ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
        ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
        ((nb078AlphaDummy403), (nb078AlphaDummy404 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy407))
          (synCphi (Class.cv (nb078AlphaDummy374)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy407))
            (synCphi (Class.cv (nb078AlphaDummy374))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy408 g))
          (synCphi (Class.cv (nb078AlphaDummy376 g)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy408 g))
            (synCphi (Class.cv (nb078AlphaDummy376 g)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy381) from
                    (by
                      unfold nb078AlphaDummy381;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0380) 0))))
                  (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy383 g) from (by
                      unfold nb078AlphaDummy383;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0381 g) 0))))
                  (TAlphaVar.there (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy382) from
                      (by
                        unfold nb078AlphaDummy382;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0380) 1))))
                    (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy384 g) from (by
                        unfold nb078AlphaDummy384;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0381 g) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy407) from (by
                          unfold nb078AlphaDummy407;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0410) 0))))
                      (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy408 g) from (by
                          unfold nb078AlphaDummy408;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0411 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy405) from (by
                            unfold nb078AlphaDummy405;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0408) 0))))
                        (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy406 g) from (by
                            unfold nb078AlphaDummy406;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0409 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy374))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy376 g))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy381) ≠ (nb078AlphaDummy388) from (by
                                        unfold nb078AlphaDummy388;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0384)
                                                1)))) (show (nb078AlphaDummy383 g) ≠
                                        (nb078AlphaDummy391 g) from (by
                                        unfold nb078AlphaDummy391;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0385 g)
                                                1)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy381) ≠ (nb078AlphaDummy387) from
                                        (by
                                          unfold nb078AlphaDummy387;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0384)
                                                  0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy390 g) from (by
                                          unfold nb078AlphaDummy390;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0385 g) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy381) ≠
        (nb078AlphaDummy385) from (by
          unfold nb078AlphaDummy385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0382) 0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy386 g) from (by
          unfold nb078AlphaDummy386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0383 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb078AlphaDummy389),
        (nb078AlphaDummy392 g)), ((nb078AlphaDummy388), (nb078AlphaDummy391 g)),
                                        ((nb078AlphaDummy387), (nb078AlphaDummy390 g)),
                                        ((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                                        ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                                        ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                                        ((nb078AlphaDummy407), (nb078AlphaDummy408 g)),
                                        ((nb078AlphaDummy405), (nb078AlphaDummy406 g)),
                                        ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                                        ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                                        ((nb078AlphaDummy403), (nb078AlphaDummy404 g)),
                                        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy388) ≠
        (nb078AlphaDummy395) from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy395)
        from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy395) from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy395)
        from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb078AlphaDummy389), (nb078AlphaDummy392 g)),
        ((nb078AlphaDummy388), (nb078AlphaDummy391 g)), ((nb078AlphaDummy387),
        (nb078AlphaDummy390 g)), ((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
        ((nb078AlphaDummy381), (nb078AlphaDummy383 g)), ((nb078AlphaDummy382),
        (nb078AlphaDummy384 g)), ((nb078AlphaDummy407), (nb078AlphaDummy408 g)),
        ((nb078AlphaDummy405), (nb078AlphaDummy406 g)), ((nb078AlphaDummy374),
        (nb078AlphaDummy376 g)), ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
        ((nb078AlphaDummy403), (nb078AlphaDummy404 g)), ((nb078AlphaDummy377),
        (nb078AlphaDummy378 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)), ((nb078AlphaDummy287),
        (nb078AlphaDummy290 g)), ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy388) ≠
        (nb078AlphaDummy399) from (by
          unfold
            nb078AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy400 g) from (by
          unfold
            nb078AlphaDummy400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy399)
        from (by
          unfold
            nb078AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy400 g) from (by
          unfold
            nb078AlphaDummy400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy401) from (by
          unfold
            nb078AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy402 g) from (by
          unfold
            nb078AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠
        (nb078AlphaDummy401) from (by
          unfold
            nb078AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy402 g) from (by
          unfold
            nb078AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                                unfold nb078AlphaDummy385;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                            (show (nb078AlphaDummy383 g) ≠ (nb078AlphaDummy386 g) from (by
                                unfold nb078AlphaDummy386;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                            ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                            ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                            ((nb078AlphaDummy407), (nb078AlphaDummy408 g)),
                            ((nb078AlphaDummy405), (nb078AlphaDummy406 g)),
                            ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                            ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                            ((nb078AlphaDummy403), (nb078AlphaDummy404 g)),
                            ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
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
                          (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                              unfold nb078AlphaDummy385;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                          (show (nb078AlphaDummy383 g) ≠ (nb078AlphaDummy386 g) from (by
                              unfold nb078AlphaDummy386;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                                unfold nb078AlphaDummy385;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                            (show (nb078AlphaDummy383 g) ≠ (nb078AlphaDummy386 g) from (by
                                unfold nb078AlphaDummy386;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                            ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                            ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                            ((nb078AlphaDummy407), (nb078AlphaDummy408 g)),
                            ((nb078AlphaDummy405), (nb078AlphaDummy406 g)),
                            ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                            ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                            ((nb078AlphaDummy403), (nb078AlphaDummy404 g)),
                            ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
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
                    (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy381) from (by
                        unfold nb078AlphaDummy381;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0380) 0))))
                    (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy383 g) from (by
                        unfold nb078AlphaDummy383;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0381 g) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy382) from (by
                          unfold nb078AlphaDummy382;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0380) 1))))
                      (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy384 g) from (by
                          unfold nb078AlphaDummy384;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0381 g) 1))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy407) from (by
                            unfold nb078AlphaDummy407;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0410) 0))))
                        (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy408 g) from (by
                            unfold nb078AlphaDummy408;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0411 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy405) from (by
                              unfold nb078AlphaDummy405;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0408) 0))))
                          (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy406 g) from (by
                              unfold nb078AlphaDummy406;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0409 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy374))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy376 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078AlphaDummy381) ≠ (nb078AlphaDummy388) from
                                        (by
                                          unfold nb078AlphaDummy388;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0384)
                                                  1)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy391 g) from (by
                                          unfold nb078AlphaDummy391;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0385 g) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy381) ≠
        (nb078AlphaDummy387) from (by
          unfold nb078AlphaDummy387;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy390 g) from (by
          unfold nb078AlphaDummy390;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
          unfold nb078AlphaDummy385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0382) 0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy386 g) from (by
          unfold nb078AlphaDummy386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0383 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb078AlphaDummy389),
        (nb078AlphaDummy392 g)), ((nb078AlphaDummy388), (nb078AlphaDummy391 g)),
        ((nb078AlphaDummy387), (nb078AlphaDummy390 g)), ((nb078AlphaDummy385),
        (nb078AlphaDummy386 g)), ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
        ((nb078AlphaDummy382), (nb078AlphaDummy384 g)), ((nb078AlphaDummy407),
        (nb078AlphaDummy408 g)), ((nb078AlphaDummy405), (nb078AlphaDummy406 g)),
        ((nb078AlphaDummy374), (nb078AlphaDummy376 g)), ((nb078AlphaDummy373),
        (nb078AlphaDummy375 g)), ((nb078AlphaDummy403), (nb078AlphaDummy404 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy289),
        (nb078AlphaDummy292 g)), ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)), ((nb078AlphaDummy293),
        (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy388) ≠
        (nb078AlphaDummy395) from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy395)
        from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy395) from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy395)
        from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy389), (nb078AlphaDummy392 g)), ((nb078AlphaDummy388),
        (nb078AlphaDummy391 g)), ((nb078AlphaDummy387), (nb078AlphaDummy390 g)),
        ((nb078AlphaDummy385), (nb078AlphaDummy386 g)), ((nb078AlphaDummy381),
        (nb078AlphaDummy383 g)), ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
        ((nb078AlphaDummy407), (nb078AlphaDummy408 g)), ((nb078AlphaDummy405),
        (nb078AlphaDummy406 g)), ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
        ((nb078AlphaDummy373), (nb078AlphaDummy375 g)), ((nb078AlphaDummy403),
        (nb078AlphaDummy404 g)), ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)), ((nb078AlphaDummy367),
        (nb078AlphaDummy369 g)), ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)), ((nb078AlphaDummy288),
        (nb078AlphaDummy291 g)), ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy381))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy381))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy388) ≠
        (nb078AlphaDummy399) from (by
          unfold
            nb078AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy400 g) from (by
          unfold
            nb078AlphaDummy400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy399)
        from (by
          unfold
            nb078AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy400 g) from (by
          unfold
            nb078AlphaDummy400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy401) from (by
          unfold
            nb078AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy402 g) from (by
          unfold
            nb078AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠
        (nb078AlphaDummy401) from (by
          unfold
            nb078AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy402 g) from (by
          unfold
            nb078AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                                  unfold nb078AlphaDummy385;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                              (show (nb078AlphaDummy383 g) ≠ (nb078AlphaDummy386 g) from
                                (by
                                  unfold nb078AlphaDummy386;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                              ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                              ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                              ((nb078AlphaDummy407), (nb078AlphaDummy408 g)),
                              ((nb078AlphaDummy405), (nb078AlphaDummy406 g)),
                              ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                              ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                              ((nb078AlphaDummy403), (nb078AlphaDummy404 g)),
                              ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
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
                            (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                                unfold nb078AlphaDummy385;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                            (show (nb078AlphaDummy383 g) ≠ (nb078AlphaDummy386 g) from (by
                                unfold nb078AlphaDummy386;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                                  unfold nb078AlphaDummy385;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                              (show (nb078AlphaDummy383 g) ≠ (nb078AlphaDummy386 g) from
                                (by
                                  unfold nb078AlphaDummy386;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                              ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                              ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                              ((nb078AlphaDummy407), (nb078AlphaDummy408 g)),
                              ((nb078AlphaDummy405), (nb078AlphaDummy406 g)),
                              ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                              ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                              ((nb078AlphaDummy403), (nb078AlphaDummy404 g)),
                              ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
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
