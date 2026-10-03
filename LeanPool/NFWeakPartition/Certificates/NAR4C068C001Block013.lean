/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C068C001Block012

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C068C001Part051`. -/


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
noncomputable def nb068_split_alpha_0141 (x : Var) (y : Var) (f : Var) :
    TAlphaClass
      [((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f),
        ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Class.cab (nb068_alpha_dummy_325) (syn_wnan
          (Wff.classMem (Class.cv (nb068_alpha_dummy_325))
            (syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
              (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))))
          (Wff.classMem (Class.cv (nb068_alpha_dummy_325)) (syn_cid))))
      (Class.cab (nb068_alpha_dummy_326 f) (syn_wnan
          (Wff.classMem (Class.cv (nb068_alpha_dummy_326 f))
            (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f)))))
          (Wff.classMem (Class.cv (nb068_alpha_dummy_326 f)) (syn_cid)))) :=
  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (Ne.symm
                          (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_333) from (by
                              unfold nb068_alpha_dummy_333;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0342) 0))))) (Ne.symm
                          (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_334 f) from (by
                              unfold nb068_alpha_dummy_334;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0343 f) 0)))))
                        (TAlphaVar.there (Ne.symm
                            (show (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_333) from (by
                                unfold nb068_alpha_dummy_333;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0340) 0))))) (Ne.symm
                            (show (nb068_alpha_dummy_330 f) ≠ (nb068_alpha_dummy_334 f) from (by
                                unfold nb068_alpha_dummy_334;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0341 f) 0)))))
                          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_336) from (by
          unfold nb068_alpha_dummy_336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0344) 1)))) (show (nb068_alpha_dummy_330 f) ≠
        (nb068_alpha_dummy_338 f) from (by
          unfold nb068_alpha_dummy_338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0346 f)
                  1)))) (TAlphaVar.there (show (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_335)
        from (by
          unfold nb068_alpha_dummy_335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0344)
                  0)))) (show (nb068_alpha_dummy_330 f) ≠ (nb068_alpha_dummy_337 f) from (by
          unfold nb068_alpha_dummy_337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0346 f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_341)
        from (by
          unfold nb068_alpha_dummy_341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0348)
                  0)))) (show (nb068_alpha_dummy_330 f) ≠ (nb068_alpha_dummy_342 f) from (by
          unfold nb068_alpha_dummy_342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0349 f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_339)
        from (by
          unfold nb068_alpha_dummy_339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0345)
                  0)))) (show (nb068_alpha_dummy_330 f) ≠ (nb068_alpha_dummy_340 f) from (by
          unfold nb068_alpha_dummy_340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0347
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (Class.cv
        (nb068_alpha_dummy_000)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv
        (nb068_alpha_dummy_000))))).fv) (by decide)) (freshVar_injective
        (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv
        (nb068_alpha_dummy_328))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all
        (nb068_split_alpha_0090 x y f))))))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_336) from (by
          unfold nb068_alpha_dummy_336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0344) 1)))) (show (nb068_alpha_dummy_330 f) ≠
        (nb068_alpha_dummy_338 f) from (by
          unfold nb068_alpha_dummy_338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0346 f)
                  1)))) (TAlphaVar.there (show (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_335)
        from (by
          unfold nb068_alpha_dummy_335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0344)
                  0)))) (show (nb068_alpha_dummy_330 f) ≠ (nb068_alpha_dummy_337 f) from (by
          unfold nb068_alpha_dummy_337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0346 f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_341)
        from (by
          unfold nb068_alpha_dummy_341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0348)
                  0)))) (show (nb068_alpha_dummy_330 f) ≠ (nb068_alpha_dummy_342 f) from (by
          unfold nb068_alpha_dummy_342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0349 f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_339)
        from (by
          unfold nb068_alpha_dummy_339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0345)
                  0)))) (show (nb068_alpha_dummy_330 f) ≠ (nb068_alpha_dummy_340 f) from (by
          unfold nb068_alpha_dummy_340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0347
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (Class.cv
        (nb068_alpha_dummy_000)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv
        (nb068_alpha_dummy_000))))).fv) (by decide)) (freshVar_injective
        (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv
        (nb068_alpha_dummy_328))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all
        (nb068_split_alpha_0090 x y f)))))))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb068_split_alpha_0093 x y f)))))))))
                  (TAlphaWff.ex (TAlphaWff.neg (nb068_split_alpha_0140 x y f))))))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn
            [((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
              ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
              ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
              ((nb068_alpha_dummy_001), x),
              ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
            (syn_cid) (nb068_wpp_refl_0179 x y f))))))

@[expose]
noncomputable def nb068_split_alpha_0142 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_351), (nb068_alpha_dummy_354 f)),
        ((nb068_alpha_dummy_350), (nb068_alpha_dummy_353 f)),
        ((nb068_alpha_dummy_349), (nb068_alpha_dummy_352 f)),
        ((nb068_alpha_dummy_347), (nb068_alpha_dummy_348 f)),
        ((nb068_alpha_dummy_343), (nb068_alpha_dummy_345 f)),
        ((nb068_alpha_dummy_344), (nb068_alpha_dummy_346 f)),
        ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)),
        ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)),
        ((nb068_alpha_dummy_341), (nb068_alpha_dummy_342 f)),
        ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_350)) (Class.cv (nb068_alpha_dummy_351)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_349))
            (syn_cun (Class.cv (nb068_alpha_dummy_350)) (Class.cv (nb068_alpha_dummy_351))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_353 f))
            (Class.cv (nb068_alpha_dummy_354 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_352 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_353 f))
              (Class.cv (nb068_alpha_dummy_354 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_350) ≠ (nb068_alpha_dummy_357) from (by
                              unfold nb068_alpha_dummy_357;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0358) 0))))
                          (show (nb068_alpha_dummy_353 f) ≠ (nb068_alpha_dummy_358 f) from (by
                              unfold nb068_alpha_dummy_358;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0359 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_350) ≠ (nb068_alpha_dummy_355) from (by
                                unfold nb068_alpha_dummy_355;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0356) 0))))
                            (show (nb068_alpha_dummy_353 f) ≠ (nb068_alpha_dummy_356 f) from (by
                                unfold nb068_alpha_dummy_356;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0357 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_351) ≠ (nb068_alpha_dummy_357) from (by
                              unfold nb068_alpha_dummy_357;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0362) 0))))
                          (show (nb068_alpha_dummy_354 f) ≠ (nb068_alpha_dummy_358 f) from (by
                              unfold nb068_alpha_dummy_358;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0363 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_351) ≠ (nb068_alpha_dummy_355) from (by
                                unfold nb068_alpha_dummy_355;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0360) 0))))
                            (show (nb068_alpha_dummy_354 f) ≠ (nb068_alpha_dummy_356 f) from (by
                                unfold nb068_alpha_dummy_356;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0361 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_350) ≠ (nb068_alpha_dummy_357) from (by
                              unfold nb068_alpha_dummy_357;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0358) 0))))
                          (show (nb068_alpha_dummy_353 f) ≠ (nb068_alpha_dummy_358 f) from (by
                              unfold nb068_alpha_dummy_358;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0359 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_350) ≠ (nb068_alpha_dummy_355) from (by
                                unfold nb068_alpha_dummy_355;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0356) 0))))
                            (show (nb068_alpha_dummy_353 f) ≠ (nb068_alpha_dummy_356 f) from (by
                                unfold nb068_alpha_dummy_356;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0357 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_351) ≠ (nb068_alpha_dummy_357) from (by
                              unfold nb068_alpha_dummy_357;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0362) 0))))
                          (show (nb068_alpha_dummy_354 f) ≠ (nb068_alpha_dummy_358 f) from (by
                              unfold nb068_alpha_dummy_358;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0363 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_351) ≠ (nb068_alpha_dummy_355) from (by
                                unfold nb068_alpha_dummy_355;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0360) 0))))
                            (show (nb068_alpha_dummy_354 f) ≠ (nb068_alpha_dummy_356 f) from (by
                                unfold nb068_alpha_dummy_356;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0361 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_351), (nb068_alpha_dummy_354 f)),
          ((nb068_alpha_dummy_350), (nb068_alpha_dummy_353 f)),
          ((nb068_alpha_dummy_349), (nb068_alpha_dummy_352 f)),
          ((nb068_alpha_dummy_347), (nb068_alpha_dummy_348 f)),
          ((nb068_alpha_dummy_343), (nb068_alpha_dummy_345 f)),
          ((nb068_alpha_dummy_344), (nb068_alpha_dummy_346 f)),
          ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)),
          ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)),
          ((nb068_alpha_dummy_341), (nb068_alpha_dummy_342 f)),
          ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)),
          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_350) ≠ (nb068_alpha_dummy_361) from (by
                                unfold nb068_alpha_dummy_361;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0366) 0))))
                            (show (nb068_alpha_dummy_353 f) ≠ (nb068_alpha_dummy_362 f) from (by
                                unfold nb068_alpha_dummy_362;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0367 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_350) ≠ (nb068_alpha_dummy_359) from (by
                                  unfold nb068_alpha_dummy_359;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0364) 0))))
                              (show (nb068_alpha_dummy_353 f) ≠ (nb068_alpha_dummy_360 f) from
                                (by
                                  unfold nb068_alpha_dummy_360;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0365 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_350) ≠ (nb068_alpha_dummy_361) from (by
                                unfold nb068_alpha_dummy_361;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0366) 0))))
                            (show (nb068_alpha_dummy_353 f) ≠ (nb068_alpha_dummy_362 f) from (by
                                unfold nb068_alpha_dummy_362;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0367 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_350) ≠ (nb068_alpha_dummy_359) from (by
                                  unfold nb068_alpha_dummy_359;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0364) 0))))
                              (show (nb068_alpha_dummy_353 f) ≠ (nb068_alpha_dummy_360 f) from
                                (by
                                  unfold nb068_alpha_dummy_360;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0365 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_351) ≠ (nb068_alpha_dummy_363) from (by
                                unfold nb068_alpha_dummy_363;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0370) 0))))
                            (show (nb068_alpha_dummy_354 f) ≠ (nb068_alpha_dummy_364 f) from (by
                                unfold nb068_alpha_dummy_364;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0371 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_351) ≠ (nb068_alpha_dummy_359) from (by
                                  unfold nb068_alpha_dummy_359;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0368) 0))))
                              (show (nb068_alpha_dummy_354 f) ≠ (nb068_alpha_dummy_360 f) from
                                (by
                                  unfold nb068_alpha_dummy_360;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0369 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_351) ≠ (nb068_alpha_dummy_363) from (by
                                unfold nb068_alpha_dummy_363;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0370) 0))))
                            (show (nb068_alpha_dummy_354 f) ≠ (nb068_alpha_dummy_364 f) from (by
                                unfold nb068_alpha_dummy_364;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0371 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_351) ≠ (nb068_alpha_dummy_359) from (by
                                  unfold nb068_alpha_dummy_359;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0368) 0))))
                              (show (nb068_alpha_dummy_354 f) ≠ (nb068_alpha_dummy_360 f) from
                                (by
                                  unfold nb068_alpha_dummy_360;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0369 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0143 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)),
        ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)),
        ((nb068_alpha_dummy_341), (nb068_alpha_dummy_342 f)),
        ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
        (syn_cphi (Class.cv (nb068_alpha_dummy_336))))
      (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
        (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪
            ((Class.cv (nb068_alpha_dummy_331 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068_alpha_dummy_336) ≠ (nb068_alpha_dummy_343) from (by
                    unfold nb068_alpha_dummy_343;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0350) 0))))
                (show (nb068_alpha_dummy_338 f) ≠ (nb068_alpha_dummy_345 f) from (by
                    unfold nb068_alpha_dummy_345;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0351 f) 0))))
                (TAlphaVar.there (show (nb068_alpha_dummy_336) ≠ (nb068_alpha_dummy_344) from
                    (by
                      unfold nb068_alpha_dummy_344;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0350) 1))))
                  (show (nb068_alpha_dummy_338 f) ≠ (nb068_alpha_dummy_346 f) from (by
                      unfold nb068_alpha_dummy_346;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0351 f) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb068_alpha_dummy_336))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb068_alpha_dummy_338 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068_alpha_dummy_343) ≠ (nb068_alpha_dummy_350) from
                                    (by
                                      unfold nb068_alpha_dummy_350;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0354)
                                              1)))) (show
                                    (nb068_alpha_dummy_345 f) ≠ (nb068_alpha_dummy_353 f) from
                                    (by
                                      unfold nb068_alpha_dummy_353;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0355 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_343) ≠ (nb068_alpha_dummy_349) from (by
                                        unfold nb068_alpha_dummy_349;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0354)
                                                0)))) (show (nb068_alpha_dummy_345 f) ≠
                                        (nb068_alpha_dummy_352 f) from (by
                                        unfold nb068_alpha_dummy_352;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0355 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_343) ≠ (nb068_alpha_dummy_347) from
                                        (by
                                          unfold nb068_alpha_dummy_347;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0352)
                                                  0)))) (show (nb068_alpha_dummy_345 f) ≠
        (nb068_alpha_dummy_348 f) from (by
                                          unfold nb068_alpha_dummy_348;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0353 f) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((nb068_alpha_dummy_351), (nb068_alpha_dummy_354 f)),
                                      ((nb068_alpha_dummy_350), (nb068_alpha_dummy_353 f)),
                                      ((nb068_alpha_dummy_349), (nb068_alpha_dummy_352 f)),
                                      ((nb068_alpha_dummy_347), (nb068_alpha_dummy_348 f)),
                                      ((nb068_alpha_dummy_343), (nb068_alpha_dummy_345 f)),
                                      ((nb068_alpha_dummy_344), (nb068_alpha_dummy_346 f)),
                                      ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)),
                                      ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)),
                                      ((nb068_alpha_dummy_341), (nb068_alpha_dummy_342 f)),
                                      ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)),
                                      ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                                      ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                                      ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                                      ((nb068_alpha_dummy_000), f),
                                      ((nb068_alpha_dummy_002), y),
                                      ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                        (nb068_alpha_dummy_004 x y f))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb068_split_alpha_0142 x y f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068_alpha_dummy_343) ≠ (nb068_alpha_dummy_347) from (by
                              unfold nb068_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0352) 0))))
                          (show (nb068_alpha_dummy_345 f) ≠ (nb068_alpha_dummy_348 f) from (by
                              unfold nb068_alpha_dummy_348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0353 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_347), (nb068_alpha_dummy_348 f)),
                          ((nb068_alpha_dummy_343), (nb068_alpha_dummy_345 f)),
                          ((nb068_alpha_dummy_344), (nb068_alpha_dummy_346 f)),
                          ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)),
                          ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)),
                          ((nb068_alpha_dummy_341), (nb068_alpha_dummy_342 f)),
                          ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)),
                          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_343) ≠ (nb068_alpha_dummy_347) from (by
                            unfold nb068_alpha_dummy_347;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0352) 0))))
                        (show (nb068_alpha_dummy_345 f) ≠ (nb068_alpha_dummy_348 f) from (by
                            unfold nb068_alpha_dummy_348;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0353 f) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068_alpha_dummy_343) ≠ (nb068_alpha_dummy_347) from (by
                              unfold nb068_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0352) 0))))
                          (show (nb068_alpha_dummy_345 f) ≠ (nb068_alpha_dummy_348 f) from (by
                              unfold nb068_alpha_dummy_348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0353 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_347), (nb068_alpha_dummy_348 f)),
                          ((nb068_alpha_dummy_343), (nb068_alpha_dummy_345 f)),
                          ((nb068_alpha_dummy_344), (nb068_alpha_dummy_346 f)),
                          ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)),
                          ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)),
                          ((nb068_alpha_dummy_341), (nb068_alpha_dummy_342 f)),
                          ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)),
                          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0144 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_351), (nb068_alpha_dummy_354 f)),
        ((nb068_alpha_dummy_350), (nb068_alpha_dummy_353 f)),
        ((nb068_alpha_dummy_349), (nb068_alpha_dummy_352 f)),
        ((nb068_alpha_dummy_347), (nb068_alpha_dummy_348 f)),
        ((nb068_alpha_dummy_343), (nb068_alpha_dummy_345 f)),
        ((nb068_alpha_dummy_344), (nb068_alpha_dummy_346 f)),
        ((nb068_alpha_dummy_369), (nb068_alpha_dummy_370 f)),
        ((nb068_alpha_dummy_367), (nb068_alpha_dummy_368 f)),
        ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)),
        ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)),
        ((nb068_alpha_dummy_365), (nb068_alpha_dummy_366 f)),
        ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_350)) (Class.cv (nb068_alpha_dummy_351)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_349))
            (syn_cun (Class.cv (nb068_alpha_dummy_350)) (Class.cv (nb068_alpha_dummy_351))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_353 f))
            (Class.cv (nb068_alpha_dummy_354 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_352 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_353 f))
              (Class.cv (nb068_alpha_dummy_354 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_350) ≠ (nb068_alpha_dummy_357) from (by
                              unfold nb068_alpha_dummy_357;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0358) 0))))
                          (show (nb068_alpha_dummy_353 f) ≠ (nb068_alpha_dummy_358 f) from (by
                              unfold nb068_alpha_dummy_358;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0359 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_350) ≠ (nb068_alpha_dummy_355) from (by
                                unfold nb068_alpha_dummy_355;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0356) 0))))
                            (show (nb068_alpha_dummy_353 f) ≠ (nb068_alpha_dummy_356 f) from (by
                                unfold nb068_alpha_dummy_356;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0357 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_351) ≠ (nb068_alpha_dummy_357) from (by
                              unfold nb068_alpha_dummy_357;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0362) 0))))
                          (show (nb068_alpha_dummy_354 f) ≠ (nb068_alpha_dummy_358 f) from (by
                              unfold nb068_alpha_dummy_358;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0363 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_351) ≠ (nb068_alpha_dummy_355) from (by
                                unfold nb068_alpha_dummy_355;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0360) 0))))
                            (show (nb068_alpha_dummy_354 f) ≠ (nb068_alpha_dummy_356 f) from (by
                                unfold nb068_alpha_dummy_356;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0361 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_350) ≠ (nb068_alpha_dummy_357) from (by
                              unfold nb068_alpha_dummy_357;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0358) 0))))
                          (show (nb068_alpha_dummy_353 f) ≠ (nb068_alpha_dummy_358 f) from (by
                              unfold nb068_alpha_dummy_358;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0359 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_350) ≠ (nb068_alpha_dummy_355) from (by
                                unfold nb068_alpha_dummy_355;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0356) 0))))
                            (show (nb068_alpha_dummy_353 f) ≠ (nb068_alpha_dummy_356 f) from (by
                                unfold nb068_alpha_dummy_356;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0357 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_351) ≠ (nb068_alpha_dummy_357) from (by
                              unfold nb068_alpha_dummy_357;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0362) 0))))
                          (show (nb068_alpha_dummy_354 f) ≠ (nb068_alpha_dummy_358 f) from (by
                              unfold nb068_alpha_dummy_358;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0363 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_351) ≠ (nb068_alpha_dummy_355) from (by
                                unfold nb068_alpha_dummy_355;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0360) 0))))
                            (show (nb068_alpha_dummy_354 f) ≠ (nb068_alpha_dummy_356 f) from (by
                                unfold nb068_alpha_dummy_356;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0361 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_351), (nb068_alpha_dummy_354 f)),
          ((nb068_alpha_dummy_350), (nb068_alpha_dummy_353 f)),
          ((nb068_alpha_dummy_349), (nb068_alpha_dummy_352 f)),
          ((nb068_alpha_dummy_347), (nb068_alpha_dummy_348 f)),
          ((nb068_alpha_dummy_343), (nb068_alpha_dummy_345 f)),
          ((nb068_alpha_dummy_344), (nb068_alpha_dummy_346 f)),
          ((nb068_alpha_dummy_369), (nb068_alpha_dummy_370 f)),
          ((nb068_alpha_dummy_367), (nb068_alpha_dummy_368 f)),
          ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)),
          ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)),
          ((nb068_alpha_dummy_365), (nb068_alpha_dummy_366 f)),
          ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)),
          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_350) ≠ (nb068_alpha_dummy_361) from (by
                                unfold nb068_alpha_dummy_361;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0366) 0))))
                            (show (nb068_alpha_dummy_353 f) ≠ (nb068_alpha_dummy_362 f) from (by
                                unfold nb068_alpha_dummy_362;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0367 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_350) ≠ (nb068_alpha_dummy_359) from (by
                                  unfold nb068_alpha_dummy_359;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0364) 0))))
                              (show (nb068_alpha_dummy_353 f) ≠ (nb068_alpha_dummy_360 f) from
                                (by
                                  unfold nb068_alpha_dummy_360;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0365 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_350) ≠ (nb068_alpha_dummy_361) from (by
                                unfold nb068_alpha_dummy_361;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0366) 0))))
                            (show (nb068_alpha_dummy_353 f) ≠ (nb068_alpha_dummy_362 f) from (by
                                unfold nb068_alpha_dummy_362;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0367 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_350) ≠ (nb068_alpha_dummy_359) from (by
                                  unfold nb068_alpha_dummy_359;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0364) 0))))
                              (show (nb068_alpha_dummy_353 f) ≠ (nb068_alpha_dummy_360 f) from
                                (by
                                  unfold nb068_alpha_dummy_360;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0365 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_351) ≠ (nb068_alpha_dummy_363) from (by
                                unfold nb068_alpha_dummy_363;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0370) 0))))
                            (show (nb068_alpha_dummy_354 f) ≠ (nb068_alpha_dummy_364 f) from (by
                                unfold nb068_alpha_dummy_364;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0371 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_351) ≠ (nb068_alpha_dummy_359) from (by
                                  unfold nb068_alpha_dummy_359;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0368) 0))))
                              (show (nb068_alpha_dummy_354 f) ≠ (nb068_alpha_dummy_360 f) from
                                (by
                                  unfold nb068_alpha_dummy_360;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0369 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_351) ≠ (nb068_alpha_dummy_363) from (by
                                unfold nb068_alpha_dummy_363;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0370) 0))))
                            (show (nb068_alpha_dummy_354 f) ≠ (nb068_alpha_dummy_364 f) from (by
                                unfold nb068_alpha_dummy_364;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0371 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_351) ≠ (nb068_alpha_dummy_359) from (by
                                  unfold nb068_alpha_dummy_359;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0368) 0))))
                              (show (nb068_alpha_dummy_354 f) ≠ (nb068_alpha_dummy_360 f) from
                                (by
                                  unfold nb068_alpha_dummy_360;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0369 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0145 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_343), (nb068_alpha_dummy_345 f)),
        ((nb068_alpha_dummy_344), (nb068_alpha_dummy_346 f)),
        ((nb068_alpha_dummy_369), (nb068_alpha_dummy_370 f)),
        ((nb068_alpha_dummy_367), (nb068_alpha_dummy_368 f)),
        ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)),
        ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)),
        ((nb068_alpha_dummy_365), (nb068_alpha_dummy_366 f)),
        ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_343))
          (Class.cv (nb068_alpha_dummy_336))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_344))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_343)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_343)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_343))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_345 f))
          (Class.cv (nb068_alpha_dummy_338 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_346 f))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_345 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_345 f)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_345 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_336) ≠ (nb068_alpha_dummy_343) from (by
              unfold nb068_alpha_dummy_343;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0350) 0))))
          (show (nb068_alpha_dummy_338 f) ≠ (nb068_alpha_dummy_345 f) from (by
              unfold nb068_alpha_dummy_345;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0351 f) 0))))
          (TAlphaVar.there (show (nb068_alpha_dummy_336) ≠ (nb068_alpha_dummy_344) from (by
                unfold nb068_alpha_dummy_344;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0350) 1))))
            (show (nb068_alpha_dummy_338 f) ≠ (nb068_alpha_dummy_346 f) from (by
                unfold nb068_alpha_dummy_346;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0351 f) 1))))
            (TAlphaVar.there (show (nb068_alpha_dummy_336) ≠ (nb068_alpha_dummy_369) from (by
                  unfold nb068_alpha_dummy_369;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0380) 0))))
              (show (nb068_alpha_dummy_338 f) ≠ (nb068_alpha_dummy_370 f) from (by
                  unfold nb068_alpha_dummy_370;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0381 f) 0))))
              (TAlphaVar.there (show (nb068_alpha_dummy_336) ≠ (nb068_alpha_dummy_367) from (by
                    unfold nb068_alpha_dummy_367;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0378) 0))))
                (show (nb068_alpha_dummy_338 f) ≠ (nb068_alpha_dummy_368 f) from (by
                    unfold nb068_alpha_dummy_368;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0379 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_336))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_338 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068_alpha_dummy_343) ≠ (nb068_alpha_dummy_350) from (by
                                  unfold nb068_alpha_dummy_350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0354) 1))))
                              (show (nb068_alpha_dummy_345 f) ≠ (nb068_alpha_dummy_353 f) from
                                (by
                                  unfold nb068_alpha_dummy_353;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0355 f) 1))))
                              (TAlphaVar.there
                                (show (nb068_alpha_dummy_343) ≠ (nb068_alpha_dummy_349) from (by
                                    unfold nb068_alpha_dummy_349;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0354) 0)))) (show
                                  (nb068_alpha_dummy_345 f) ≠ (nb068_alpha_dummy_352 f) from (by
                                    unfold nb068_alpha_dummy_352;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0355 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_343) ≠ (nb068_alpha_dummy_347) from
                                    (by
                                      unfold nb068_alpha_dummy_347;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0352)
                                              0)))) (show
                                    (nb068_alpha_dummy_345 f) ≠ (nb068_alpha_dummy_348 f) from
                                    (by
                                      unfold nb068_alpha_dummy_348;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0353 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb068_alpha_dummy_351), (nb068_alpha_dummy_354 f)),
                                  ((nb068_alpha_dummy_350), (nb068_alpha_dummy_353 f)),
                                  ((nb068_alpha_dummy_349), (nb068_alpha_dummy_352 f)),
                                  ((nb068_alpha_dummy_347), (nb068_alpha_dummy_348 f)),
                                  ((nb068_alpha_dummy_343), (nb068_alpha_dummy_345 f)),
                                  ((nb068_alpha_dummy_344), (nb068_alpha_dummy_346 f)),
                                  ((nb068_alpha_dummy_369), (nb068_alpha_dummy_370 f)),
                                  ((nb068_alpha_dummy_367), (nb068_alpha_dummy_368 f)),
                                  ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)),
                                  ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)),
                                  ((nb068_alpha_dummy_365), (nb068_alpha_dummy_366 f)),
                                  ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)),
                                  ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                                  ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                                  ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                                  ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                    (nb068_alpha_dummy_004 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068_split_alpha_0144 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068_alpha_dummy_343) ≠ (nb068_alpha_dummy_347) from (by
                          unfold nb068_alpha_dummy_347;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0352) 0))))
                      (show (nb068_alpha_dummy_345 f) ≠ (nb068_alpha_dummy_348 f) from (by
                          unfold nb068_alpha_dummy_348;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0353 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_347), (nb068_alpha_dummy_348 f)),
                      ((nb068_alpha_dummy_343), (nb068_alpha_dummy_345 f)),
                      ((nb068_alpha_dummy_344), (nb068_alpha_dummy_346 f)),
                      ((nb068_alpha_dummy_369), (nb068_alpha_dummy_370 f)),
                      ((nb068_alpha_dummy_367), (nb068_alpha_dummy_368 f)),
                      ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)),
                      ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)),
                      ((nb068_alpha_dummy_365), (nb068_alpha_dummy_366 f)),
                      ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)),
                      ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                      ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                      ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_343) ≠ (nb068_alpha_dummy_347) from
                      (by
                        unfold nb068_alpha_dummy_347;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0352) 0))))
                    (show (nb068_alpha_dummy_345 f) ≠ (nb068_alpha_dummy_348 f) from (by
                        unfold nb068_alpha_dummy_348;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0353 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_343) ≠ (nb068_alpha_dummy_347) from (by
                          unfold nb068_alpha_dummy_347;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0352) 0))))
                      (show (nb068_alpha_dummy_345 f) ≠ (nb068_alpha_dummy_348 f) from (by
                          unfold nb068_alpha_dummy_348;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0353 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_347), (nb068_alpha_dummy_348 f)),
                      ((nb068_alpha_dummy_343), (nb068_alpha_dummy_345 f)),
                      ((nb068_alpha_dummy_344), (nb068_alpha_dummy_346 f)),
                      ((nb068_alpha_dummy_369), (nb068_alpha_dummy_370 f)),
                      ((nb068_alpha_dummy_367), (nb068_alpha_dummy_368 f)),
                      ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)),
                      ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)),
                      ((nb068_alpha_dummy_365), (nb068_alpha_dummy_366 f)),
                      ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)),
                      ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                      ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                      ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part052`. -/


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
noncomputable def nb068_split_alpha_0146 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_365), (nb068_alpha_dummy_366 f)),
        ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_365))
          (Class.cab (nb068_alpha_dummy_335)
            (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_365))
            (Class.cab (nb068_alpha_dummy_335)
              (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_366 f))
          (Class.cab (nb068_alpha_dummy_337 f)
            (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_366 f))
            (Class.cab (nb068_alpha_dummy_337 f)
              (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_336) from
                    (by
                      unfold nb068_alpha_dummy_336;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0372) 1))))
                  (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_338 f) from (by
                      unfold nb068_alpha_dummy_338;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0374 f) 1))))
                  (TAlphaVar.there (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_335) from
                      (by
                        unfold nb068_alpha_dummy_335;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0372) 0))))
                    (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_337 f) from (by
                        unfold nb068_alpha_dummy_337;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0374 f) 0)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_365) from (by
                          unfold nb068_alpha_dummy_365;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0376) 0))))
                      (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_366 f) from (by
                          unfold nb068_alpha_dummy_366;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0377 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_339) from (by
                            unfold nb068_alpha_dummy_339;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0373) 0))))
                        (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_340 f) from (by
                            unfold nb068_alpha_dummy_340;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0375 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_327))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_328))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_331 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0145 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0145 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_367), (nb068_alpha_dummy_368 f)),
                          ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)),
                          ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)),
                          ((nb068_alpha_dummy_365), (nb068_alpha_dummy_366 f)),
                          ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)),
                          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_336) from
                      (by
                        unfold nb068_alpha_dummy_336;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0372) 1))))
                    (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_338 f) from (by
                        unfold nb068_alpha_dummy_338;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0374 f) 1)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_335) from (by
                          unfold nb068_alpha_dummy_335;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0372) 0))))
                      (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_337 f) from (by
                          unfold nb068_alpha_dummy_337;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0374 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_365) from (by
                            unfold nb068_alpha_dummy_365;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0376) 0))))
                        (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_366 f) from (by
                            unfold nb068_alpha_dummy_366;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0377 f) 0))))
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_339) from (by
                              unfold nb068_alpha_dummy_339;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0373) 0))))
                          (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_340 f) from (by
                              unfold nb068_alpha_dummy_340;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0375 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068_alpha_dummy_327))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_328))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_331 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0145 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0145 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb068_alpha_dummy_367), (nb068_alpha_dummy_368 f)),
                            ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)),
                            ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)),
                            ((nb068_alpha_dummy_365), (nb068_alpha_dummy_366 f)),
                            ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)),
                            ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                            ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                            ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                            ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                            ((nb068_alpha_dummy_001), x),
                            ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0147 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_387), (nb068_alpha_dummy_390 f)),
        ((nb068_alpha_dummy_386), (nb068_alpha_dummy_389 f)),
        ((nb068_alpha_dummy_385), (nb068_alpha_dummy_388 f)),
        ((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)),
        ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)),
        ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)),
        ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)),
        ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)),
        ((nb068_alpha_dummy_377), (nb068_alpha_dummy_378 f)),
        ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_386)) (Class.cv (nb068_alpha_dummy_387)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_385))
            (syn_cun (Class.cv (nb068_alpha_dummy_386)) (Class.cv (nb068_alpha_dummy_387))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_389 f))
            (Class.cv (nb068_alpha_dummy_390 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_388 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_389 f))
              (Class.cv (nb068_alpha_dummy_390 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_386) ≠ (nb068_alpha_dummy_393) from (by
                              unfold nb068_alpha_dummy_393;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0396) 0))))
                          (show (nb068_alpha_dummy_389 f) ≠ (nb068_alpha_dummy_394 f) from (by
                              unfold nb068_alpha_dummy_394;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0397 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_386) ≠ (nb068_alpha_dummy_391) from (by
                                unfold nb068_alpha_dummy_391;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0394) 0))))
                            (show (nb068_alpha_dummy_389 f) ≠ (nb068_alpha_dummy_392 f) from (by
                                unfold nb068_alpha_dummy_392;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0395 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_387) ≠ (nb068_alpha_dummy_393) from (by
                              unfold nb068_alpha_dummy_393;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0400) 0))))
                          (show (nb068_alpha_dummy_390 f) ≠ (nb068_alpha_dummy_394 f) from (by
                              unfold nb068_alpha_dummy_394;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0401 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_387) ≠ (nb068_alpha_dummy_391) from (by
                                unfold nb068_alpha_dummy_391;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0398) 0))))
                            (show (nb068_alpha_dummy_390 f) ≠ (nb068_alpha_dummy_392 f) from (by
                                unfold nb068_alpha_dummy_392;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0399 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_386) ≠ (nb068_alpha_dummy_393) from (by
                              unfold nb068_alpha_dummy_393;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0396) 0))))
                          (show (nb068_alpha_dummy_389 f) ≠ (nb068_alpha_dummy_394 f) from (by
                              unfold nb068_alpha_dummy_394;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0397 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_386) ≠ (nb068_alpha_dummy_391) from (by
                                unfold nb068_alpha_dummy_391;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0394) 0))))
                            (show (nb068_alpha_dummy_389 f) ≠ (nb068_alpha_dummy_392 f) from (by
                                unfold nb068_alpha_dummy_392;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0395 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_387) ≠ (nb068_alpha_dummy_393) from (by
                              unfold nb068_alpha_dummy_393;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0400) 0))))
                          (show (nb068_alpha_dummy_390 f) ≠ (nb068_alpha_dummy_394 f) from (by
                              unfold nb068_alpha_dummy_394;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0401 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_387) ≠ (nb068_alpha_dummy_391) from (by
                                unfold nb068_alpha_dummy_391;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0398) 0))))
                            (show (nb068_alpha_dummy_390 f) ≠ (nb068_alpha_dummy_392 f) from (by
                                unfold nb068_alpha_dummy_392;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0399 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_387), (nb068_alpha_dummy_390 f)),
          ((nb068_alpha_dummy_386), (nb068_alpha_dummy_389 f)),
          ((nb068_alpha_dummy_385), (nb068_alpha_dummy_388 f)),
          ((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)),
          ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)),
          ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)),
          ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)),
          ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)),
          ((nb068_alpha_dummy_377), (nb068_alpha_dummy_378 f)),
          ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)),
          ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_386) ≠ (nb068_alpha_dummy_397) from (by
                                unfold nb068_alpha_dummy_397;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0404) 0))))
                            (show (nb068_alpha_dummy_389 f) ≠ (nb068_alpha_dummy_398 f) from (by
                                unfold nb068_alpha_dummy_398;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0405 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_386) ≠ (nb068_alpha_dummy_395) from (by
                                  unfold nb068_alpha_dummy_395;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0402) 0))))
                              (show (nb068_alpha_dummy_389 f) ≠ (nb068_alpha_dummy_396 f) from
                                (by
                                  unfold nb068_alpha_dummy_396;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0403 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_386) ≠ (nb068_alpha_dummy_397) from (by
                                unfold nb068_alpha_dummy_397;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0404) 0))))
                            (show (nb068_alpha_dummy_389 f) ≠ (nb068_alpha_dummy_398 f) from (by
                                unfold nb068_alpha_dummy_398;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0405 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_386) ≠ (nb068_alpha_dummy_395) from (by
                                  unfold nb068_alpha_dummy_395;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0402) 0))))
                              (show (nb068_alpha_dummy_389 f) ≠ (nb068_alpha_dummy_396 f) from
                                (by
                                  unfold nb068_alpha_dummy_396;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0403 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_387) ≠ (nb068_alpha_dummy_399) from (by
                                unfold nb068_alpha_dummy_399;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0408) 0))))
                            (show (nb068_alpha_dummy_390 f) ≠ (nb068_alpha_dummy_400 f) from (by
                                unfold nb068_alpha_dummy_400;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0409 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_387) ≠ (nb068_alpha_dummy_395) from (by
                                  unfold nb068_alpha_dummy_395;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0406) 0))))
                              (show (nb068_alpha_dummy_390 f) ≠ (nb068_alpha_dummy_396 f) from
                                (by
                                  unfold nb068_alpha_dummy_396;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0407 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_387) ≠ (nb068_alpha_dummy_399) from (by
                                unfold nb068_alpha_dummy_399;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0408) 0))))
                            (show (nb068_alpha_dummy_390 f) ≠ (nb068_alpha_dummy_400 f) from (by
                                unfold nb068_alpha_dummy_400;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0409 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_387) ≠ (nb068_alpha_dummy_395) from (by
                                  unfold nb068_alpha_dummy_395;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0406) 0))))
                              (show (nb068_alpha_dummy_390 f) ≠ (nb068_alpha_dummy_396 f) from
                                (by
                                  unfold nb068_alpha_dummy_396;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0407 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0148 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)),
        ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)),
        ((nb068_alpha_dummy_377), (nb068_alpha_dummy_378 f)),
        ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
        (syn_cphi (Class.cv (nb068_alpha_dummy_372))))
      (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
        (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_329))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪
            ((Class.cv (nb068_alpha_dummy_332 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068_alpha_dummy_372) ≠ (nb068_alpha_dummy_379) from (by
                    unfold nb068_alpha_dummy_379;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0388) 0))))
                (show (nb068_alpha_dummy_374 f) ≠ (nb068_alpha_dummy_381 f) from (by
                    unfold nb068_alpha_dummy_381;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0389 f) 0))))
                (TAlphaVar.there (show (nb068_alpha_dummy_372) ≠ (nb068_alpha_dummy_380) from
                    (by
                      unfold nb068_alpha_dummy_380;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0388) 1))))
                  (show (nb068_alpha_dummy_374 f) ≠ (nb068_alpha_dummy_382 f) from (by
                      unfold nb068_alpha_dummy_382;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0389 f) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb068_alpha_dummy_372))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb068_alpha_dummy_374 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068_alpha_dummy_379) ≠ (nb068_alpha_dummy_386) from
                                    (by
                                      unfold nb068_alpha_dummy_386;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0392)
                                              1)))) (show
                                    (nb068_alpha_dummy_381 f) ≠ (nb068_alpha_dummy_389 f) from
                                    (by
                                      unfold nb068_alpha_dummy_389;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0393 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_379) ≠ (nb068_alpha_dummy_385) from (by
                                        unfold nb068_alpha_dummy_385;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0392)
                                                0)))) (show (nb068_alpha_dummy_381 f) ≠
                                        (nb068_alpha_dummy_388 f) from (by
                                        unfold nb068_alpha_dummy_388;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0393 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_379) ≠ (nb068_alpha_dummy_383) from
                                        (by
                                          unfold nb068_alpha_dummy_383;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0390)
                                                  0)))) (show (nb068_alpha_dummy_381 f) ≠
        (nb068_alpha_dummy_384 f) from (by
                                          unfold nb068_alpha_dummy_384;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0391 f) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((nb068_alpha_dummy_387), (nb068_alpha_dummy_390 f)),
                                      ((nb068_alpha_dummy_386), (nb068_alpha_dummy_389 f)),
                                      ((nb068_alpha_dummy_385), (nb068_alpha_dummy_388 f)),
                                      ((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)),
                                      ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)),
                                      ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)),
                                      ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)),
                                      ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)),
                                      ((nb068_alpha_dummy_377), (nb068_alpha_dummy_378 f)),
                                      ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)),
                                      ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                                      ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                                      ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                                      ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                                      ((nb068_alpha_dummy_000), f),
                                      ((nb068_alpha_dummy_002), y),
                                      ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                        (nb068_alpha_dummy_004 x y f))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb068_split_alpha_0147 x y f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068_alpha_dummy_379) ≠ (nb068_alpha_dummy_383) from (by
                              unfold nb068_alpha_dummy_383;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0390) 0))))
                          (show (nb068_alpha_dummy_381 f) ≠ (nb068_alpha_dummy_384 f) from (by
                              unfold nb068_alpha_dummy_384;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0391 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)),
                          ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)),
                          ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)),
                          ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)),
                          ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)),
                          ((nb068_alpha_dummy_377), (nb068_alpha_dummy_378 f)),
                          ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)),
                          ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_379) ≠ (nb068_alpha_dummy_383) from (by
                            unfold nb068_alpha_dummy_383;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0390) 0))))
                        (show (nb068_alpha_dummy_381 f) ≠ (nb068_alpha_dummy_384 f) from (by
                            unfold nb068_alpha_dummy_384;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0391 f) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068_alpha_dummy_379) ≠ (nb068_alpha_dummy_383) from (by
                              unfold nb068_alpha_dummy_383;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0390) 0))))
                          (show (nb068_alpha_dummy_381 f) ≠ (nb068_alpha_dummy_384 f) from (by
                              unfold nb068_alpha_dummy_384;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0391 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)),
                          ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)),
                          ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)),
                          ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)),
                          ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)),
                          ((nb068_alpha_dummy_377), (nb068_alpha_dummy_378 f)),
                          ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)),
                          ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0149 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_387), (nb068_alpha_dummy_390 f)),
        ((nb068_alpha_dummy_386), (nb068_alpha_dummy_389 f)),
        ((nb068_alpha_dummy_385), (nb068_alpha_dummy_388 f)),
        ((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)),
        ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)),
        ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)),
        ((nb068_alpha_dummy_405), (nb068_alpha_dummy_406 f)),
        ((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)),
        ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)),
        ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)),
        ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)),
        ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_386)) (Class.cv (nb068_alpha_dummy_387)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_385))
            (syn_cun (Class.cv (nb068_alpha_dummy_386)) (Class.cv (nb068_alpha_dummy_387))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_389 f))
            (Class.cv (nb068_alpha_dummy_390 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_388 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_389 f))
              (Class.cv (nb068_alpha_dummy_390 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_386) ≠ (nb068_alpha_dummy_393) from (by
                              unfold nb068_alpha_dummy_393;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0396) 0))))
                          (show (nb068_alpha_dummy_389 f) ≠ (nb068_alpha_dummy_394 f) from (by
                              unfold nb068_alpha_dummy_394;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0397 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_386) ≠ (nb068_alpha_dummy_391) from (by
                                unfold nb068_alpha_dummy_391;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0394) 0))))
                            (show (nb068_alpha_dummy_389 f) ≠ (nb068_alpha_dummy_392 f) from (by
                                unfold nb068_alpha_dummy_392;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0395 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_387) ≠ (nb068_alpha_dummy_393) from (by
                              unfold nb068_alpha_dummy_393;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0400) 0))))
                          (show (nb068_alpha_dummy_390 f) ≠ (nb068_alpha_dummy_394 f) from (by
                              unfold nb068_alpha_dummy_394;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0401 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_387) ≠ (nb068_alpha_dummy_391) from (by
                                unfold nb068_alpha_dummy_391;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0398) 0))))
                            (show (nb068_alpha_dummy_390 f) ≠ (nb068_alpha_dummy_392 f) from (by
                                unfold nb068_alpha_dummy_392;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0399 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_386) ≠ (nb068_alpha_dummy_393) from (by
                              unfold nb068_alpha_dummy_393;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0396) 0))))
                          (show (nb068_alpha_dummy_389 f) ≠ (nb068_alpha_dummy_394 f) from (by
                              unfold nb068_alpha_dummy_394;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0397 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_386) ≠ (nb068_alpha_dummy_391) from (by
                                unfold nb068_alpha_dummy_391;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0394) 0))))
                            (show (nb068_alpha_dummy_389 f) ≠ (nb068_alpha_dummy_392 f) from (by
                                unfold nb068_alpha_dummy_392;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0395 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_387) ≠ (nb068_alpha_dummy_393) from (by
                              unfold nb068_alpha_dummy_393;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0400) 0))))
                          (show (nb068_alpha_dummy_390 f) ≠ (nb068_alpha_dummy_394 f) from (by
                              unfold nb068_alpha_dummy_394;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0401 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_387) ≠ (nb068_alpha_dummy_391) from (by
                                unfold nb068_alpha_dummy_391;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0398) 0))))
                            (show (nb068_alpha_dummy_390 f) ≠ (nb068_alpha_dummy_392 f) from (by
                                unfold nb068_alpha_dummy_392;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0399 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_387), (nb068_alpha_dummy_390 f)),
          ((nb068_alpha_dummy_386), (nb068_alpha_dummy_389 f)),
          ((nb068_alpha_dummy_385), (nb068_alpha_dummy_388 f)),
          ((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)),
          ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)),
          ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)),
          ((nb068_alpha_dummy_405), (nb068_alpha_dummy_406 f)),
          ((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)),
          ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)),
          ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)),
          ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)),
          ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)),
          ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_386) ≠ (nb068_alpha_dummy_397) from (by
                                unfold nb068_alpha_dummy_397;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0404) 0))))
                            (show (nb068_alpha_dummy_389 f) ≠ (nb068_alpha_dummy_398 f) from (by
                                unfold nb068_alpha_dummy_398;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0405 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_386) ≠ (nb068_alpha_dummy_395) from (by
                                  unfold nb068_alpha_dummy_395;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0402) 0))))
                              (show (nb068_alpha_dummy_389 f) ≠ (nb068_alpha_dummy_396 f) from
                                (by
                                  unfold nb068_alpha_dummy_396;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0403 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_386) ≠ (nb068_alpha_dummy_397) from (by
                                unfold nb068_alpha_dummy_397;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0404) 0))))
                            (show (nb068_alpha_dummy_389 f) ≠ (nb068_alpha_dummy_398 f) from (by
                                unfold nb068_alpha_dummy_398;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0405 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_386) ≠ (nb068_alpha_dummy_395) from (by
                                  unfold nb068_alpha_dummy_395;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0402) 0))))
                              (show (nb068_alpha_dummy_389 f) ≠ (nb068_alpha_dummy_396 f) from
                                (by
                                  unfold nb068_alpha_dummy_396;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0403 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_387) ≠ (nb068_alpha_dummy_399) from (by
                                unfold nb068_alpha_dummy_399;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0408) 0))))
                            (show (nb068_alpha_dummy_390 f) ≠ (nb068_alpha_dummy_400 f) from (by
                                unfold nb068_alpha_dummy_400;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0409 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_387) ≠ (nb068_alpha_dummy_395) from (by
                                  unfold nb068_alpha_dummy_395;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0406) 0))))
                              (show (nb068_alpha_dummy_390 f) ≠ (nb068_alpha_dummy_396 f) from
                                (by
                                  unfold nb068_alpha_dummy_396;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0407 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_387) ≠ (nb068_alpha_dummy_399) from (by
                                unfold nb068_alpha_dummy_399;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0408) 0))))
                            (show (nb068_alpha_dummy_390 f) ≠ (nb068_alpha_dummy_400 f) from (by
                                unfold nb068_alpha_dummy_400;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0409 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_387) ≠ (nb068_alpha_dummy_395) from (by
                                  unfold nb068_alpha_dummy_395;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0406) 0))))
                              (show (nb068_alpha_dummy_390 f) ≠ (nb068_alpha_dummy_396 f) from
                                (by
                                  unfold nb068_alpha_dummy_396;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0407 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part053`. -/


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
noncomputable def nb068_split_alpha_0150 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)),
        ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)),
        ((nb068_alpha_dummy_405), (nb068_alpha_dummy_406 f)),
        ((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)),
        ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)),
        ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)),
        ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)),
        ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_379))
          (Class.cv (nb068_alpha_dummy_372))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_380))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_379)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_379)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_379))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_381 f))
          (Class.cv (nb068_alpha_dummy_374 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_382 f))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_381 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_381 f)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_381 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_372) ≠ (nb068_alpha_dummy_379) from (by
              unfold nb068_alpha_dummy_379;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0388) 0))))
          (show (nb068_alpha_dummy_374 f) ≠ (nb068_alpha_dummy_381 f) from (by
              unfold nb068_alpha_dummy_381;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0389 f) 0))))
          (TAlphaVar.there (show (nb068_alpha_dummy_372) ≠ (nb068_alpha_dummy_380) from (by
                unfold nb068_alpha_dummy_380;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0388) 1))))
            (show (nb068_alpha_dummy_374 f) ≠ (nb068_alpha_dummy_382 f) from (by
                unfold nb068_alpha_dummy_382;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0389 f) 1))))
            (TAlphaVar.there (show (nb068_alpha_dummy_372) ≠ (nb068_alpha_dummy_405) from (by
                  unfold nb068_alpha_dummy_405;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0418) 0))))
              (show (nb068_alpha_dummy_374 f) ≠ (nb068_alpha_dummy_406 f) from (by
                  unfold nb068_alpha_dummy_406;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0419 f) 0))))
              (TAlphaVar.there (show (nb068_alpha_dummy_372) ≠ (nb068_alpha_dummy_403) from (by
                    unfold nb068_alpha_dummy_403;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0416) 0))))
                (show (nb068_alpha_dummy_374 f) ≠ (nb068_alpha_dummy_404 f) from (by
                    unfold nb068_alpha_dummy_404;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0417 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_372))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_374 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068_alpha_dummy_379) ≠ (nb068_alpha_dummy_386) from (by
                                  unfold nb068_alpha_dummy_386;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0392) 1))))
                              (show (nb068_alpha_dummy_381 f) ≠ (nb068_alpha_dummy_389 f) from
                                (by
                                  unfold nb068_alpha_dummy_389;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0393 f) 1))))
                              (TAlphaVar.there
                                (show (nb068_alpha_dummy_379) ≠ (nb068_alpha_dummy_385) from (by
                                    unfold nb068_alpha_dummy_385;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0392) 0)))) (show
                                  (nb068_alpha_dummy_381 f) ≠ (nb068_alpha_dummy_388 f) from (by
                                    unfold nb068_alpha_dummy_388;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0393 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_379) ≠ (nb068_alpha_dummy_383) from
                                    (by
                                      unfold nb068_alpha_dummy_383;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0390)
                                              0)))) (show
                                    (nb068_alpha_dummy_381 f) ≠ (nb068_alpha_dummy_384 f) from
                                    (by
                                      unfold nb068_alpha_dummy_384;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0391 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb068_alpha_dummy_387), (nb068_alpha_dummy_390 f)),
                                  ((nb068_alpha_dummy_386), (nb068_alpha_dummy_389 f)),
                                  ((nb068_alpha_dummy_385), (nb068_alpha_dummy_388 f)),
                                  ((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)),
                                  ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)),
                                  ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)),
                                  ((nb068_alpha_dummy_405), (nb068_alpha_dummy_406 f)),
                                  ((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)),
                                  ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)),
                                  ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)),
                                  ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)),
                                  ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)),
                                  ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                                  ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                                  ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                                  ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                                  ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                    (nb068_alpha_dummy_004 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068_split_alpha_0149 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068_alpha_dummy_379) ≠ (nb068_alpha_dummy_383) from (by
                          unfold nb068_alpha_dummy_383;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0390) 0))))
                      (show (nb068_alpha_dummy_381 f) ≠ (nb068_alpha_dummy_384 f) from (by
                          unfold nb068_alpha_dummy_384;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0391 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)),
                      ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)),
                      ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)),
                      ((nb068_alpha_dummy_405), (nb068_alpha_dummy_406 f)),
                      ((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)),
                      ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)),
                      ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)),
                      ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)),
                      ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)),
                      ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                      ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                      ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                      ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_379) ≠ (nb068_alpha_dummy_383) from
                      (by
                        unfold nb068_alpha_dummy_383;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0390) 0))))
                    (show (nb068_alpha_dummy_381 f) ≠ (nb068_alpha_dummy_384 f) from (by
                        unfold nb068_alpha_dummy_384;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0391 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_379) ≠ (nb068_alpha_dummy_383) from (by
                          unfold nb068_alpha_dummy_383;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0390) 0))))
                      (show (nb068_alpha_dummy_381 f) ≠ (nb068_alpha_dummy_384 f) from (by
                          unfold nb068_alpha_dummy_384;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0391 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)),
                      ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)),
                      ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)),
                      ((nb068_alpha_dummy_405), (nb068_alpha_dummy_406 f)),
                      ((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)),
                      ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)),
                      ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)),
                      ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)),
                      ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)),
                      ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                      ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                      ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                      ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb068_split_alpha_0151 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)),
        ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_401))
          (Class.cab (nb068_alpha_dummy_371)
            (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_401))
            (Class.cab (nb068_alpha_dummy_371)
              (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_402 f))
          (Class.cab (nb068_alpha_dummy_373 f)
            (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_402 f))
            (Class.cab (nb068_alpha_dummy_373 f)
              (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068_alpha_dummy_329) ≠ (nb068_alpha_dummy_372) from
                    (by
                      unfold nb068_alpha_dummy_372;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0410) 1))))
                  (show (nb068_alpha_dummy_332 f) ≠ (nb068_alpha_dummy_374 f) from (by
                      unfold nb068_alpha_dummy_374;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0412 f) 1))))
                  (TAlphaVar.there (show (nb068_alpha_dummy_329) ≠ (nb068_alpha_dummy_371) from
                      (by
                        unfold nb068_alpha_dummy_371;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0410) 0))))
                    (show (nb068_alpha_dummy_332 f) ≠ (nb068_alpha_dummy_373 f) from (by
                        unfold nb068_alpha_dummy_373;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0412 f) 0)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_329) ≠ (nb068_alpha_dummy_401) from (by
                          unfold nb068_alpha_dummy_401;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0414) 0))))
                      (show (nb068_alpha_dummy_332 f) ≠ (nb068_alpha_dummy_402 f) from (by
                          unfold nb068_alpha_dummy_402;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0415 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_329) ≠ (nb068_alpha_dummy_375) from (by
                            unfold nb068_alpha_dummy_375;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0411) 0))))
                        (show (nb068_alpha_dummy_332 f) ≠ (nb068_alpha_dummy_376 f) from (by
                            unfold nb068_alpha_dummy_376;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0413 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_327))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_329))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_332 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0150 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0150 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)),
                          ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)),
                          ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)),
                          ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)),
                          ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)),
                          ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_329) ≠ (nb068_alpha_dummy_372) from
                      (by
                        unfold nb068_alpha_dummy_372;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0410) 1))))
                    (show (nb068_alpha_dummy_332 f) ≠ (nb068_alpha_dummy_374 f) from (by
                        unfold nb068_alpha_dummy_374;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0412 f) 1)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_329) ≠ (nb068_alpha_dummy_371) from (by
                          unfold nb068_alpha_dummy_371;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0410) 0))))
                      (show (nb068_alpha_dummy_332 f) ≠ (nb068_alpha_dummy_373 f) from (by
                          unfold nb068_alpha_dummy_373;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0412 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_329) ≠ (nb068_alpha_dummy_401) from (by
                            unfold nb068_alpha_dummy_401;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0414) 0))))
                        (show (nb068_alpha_dummy_332 f) ≠ (nb068_alpha_dummy_402 f) from (by
                            unfold nb068_alpha_dummy_402;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0415 f) 0))))
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_329) ≠ (nb068_alpha_dummy_375) from (by
                              unfold nb068_alpha_dummy_375;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0411) 0))))
                          (show (nb068_alpha_dummy_332 f) ≠ (nb068_alpha_dummy_376 f) from (by
                              unfold nb068_alpha_dummy_376;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0413 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068_alpha_dummy_327))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_329))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_332 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0150 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0150 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)),
                            ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)),
                            ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)),
                            ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)),
                            ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)),
                            ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                            ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                            ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                            ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                            ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                            ((nb068_alpha_dummy_001), x),
                            ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0152 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_429), (nb068_alpha_dummy_432 f)),
        ((nb068_alpha_dummy_428), (nb068_alpha_dummy_431 f)),
        ((nb068_alpha_dummy_427), (nb068_alpha_dummy_430 f)),
        ((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)),
        ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)),
        ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)),
        ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)),
        ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)),
        ((nb068_alpha_dummy_419), (nb068_alpha_dummy_420 f)),
        ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)),
        ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_428)) (Class.cv (nb068_alpha_dummy_429)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_427))
            (syn_cun (Class.cv (nb068_alpha_dummy_428)) (Class.cv (nb068_alpha_dummy_429))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_431 f))
            (Class.cv (nb068_alpha_dummy_432 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_430 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_431 f))
              (Class.cv (nb068_alpha_dummy_432 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_428) ≠ (nb068_alpha_dummy_435) from (by
                              unfold nb068_alpha_dummy_435;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0438) 0))))
                          (show (nb068_alpha_dummy_431 f) ≠ (nb068_alpha_dummy_436 f) from (by
                              unfold nb068_alpha_dummy_436;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0439 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_428) ≠ (nb068_alpha_dummy_433) from (by
                                unfold nb068_alpha_dummy_433;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0436) 0))))
                            (show (nb068_alpha_dummy_431 f) ≠ (nb068_alpha_dummy_434 f) from (by
                                unfold nb068_alpha_dummy_434;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0437 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_429) ≠ (nb068_alpha_dummy_435) from (by
                              unfold nb068_alpha_dummy_435;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0442) 0))))
                          (show (nb068_alpha_dummy_432 f) ≠ (nb068_alpha_dummy_436 f) from (by
                              unfold nb068_alpha_dummy_436;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0443 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_429) ≠ (nb068_alpha_dummy_433) from (by
                                unfold nb068_alpha_dummy_433;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0440) 0))))
                            (show (nb068_alpha_dummy_432 f) ≠ (nb068_alpha_dummy_434 f) from (by
                                unfold nb068_alpha_dummy_434;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0441 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_428) ≠ (nb068_alpha_dummy_435) from (by
                              unfold nb068_alpha_dummy_435;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0438) 0))))
                          (show (nb068_alpha_dummy_431 f) ≠ (nb068_alpha_dummy_436 f) from (by
                              unfold nb068_alpha_dummy_436;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0439 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_428) ≠ (nb068_alpha_dummy_433) from (by
                                unfold nb068_alpha_dummy_433;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0436) 0))))
                            (show (nb068_alpha_dummy_431 f) ≠ (nb068_alpha_dummy_434 f) from (by
                                unfold nb068_alpha_dummy_434;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0437 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_429) ≠ (nb068_alpha_dummy_435) from (by
                              unfold nb068_alpha_dummy_435;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0442) 0))))
                          (show (nb068_alpha_dummy_432 f) ≠ (nb068_alpha_dummy_436 f) from (by
                              unfold nb068_alpha_dummy_436;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0443 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_429) ≠ (nb068_alpha_dummy_433) from (by
                                unfold nb068_alpha_dummy_433;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0440) 0))))
                            (show (nb068_alpha_dummy_432 f) ≠ (nb068_alpha_dummy_434 f) from (by
                                unfold nb068_alpha_dummy_434;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0441 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_429), (nb068_alpha_dummy_432 f)),
          ((nb068_alpha_dummy_428), (nb068_alpha_dummy_431 f)),
          ((nb068_alpha_dummy_427), (nb068_alpha_dummy_430 f)),
          ((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)),
          ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)),
          ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)),
          ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)),
          ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)),
          ((nb068_alpha_dummy_419), (nb068_alpha_dummy_420 f)),
          ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)),
          ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
          ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
          ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
          ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_428) ≠ (nb068_alpha_dummy_439) from (by
                                unfold nb068_alpha_dummy_439;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0446) 0))))
                            (show (nb068_alpha_dummy_431 f) ≠ (nb068_alpha_dummy_440 f) from (by
                                unfold nb068_alpha_dummy_440;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0447 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_428) ≠ (nb068_alpha_dummy_437) from (by
                                  unfold nb068_alpha_dummy_437;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0444) 0))))
                              (show (nb068_alpha_dummy_431 f) ≠ (nb068_alpha_dummy_438 f) from
                                (by
                                  unfold nb068_alpha_dummy_438;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0445 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_428) ≠ (nb068_alpha_dummy_439) from (by
                                unfold nb068_alpha_dummy_439;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0446) 0))))
                            (show (nb068_alpha_dummy_431 f) ≠ (nb068_alpha_dummy_440 f) from (by
                                unfold nb068_alpha_dummy_440;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0447 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_428) ≠ (nb068_alpha_dummy_437) from (by
                                  unfold nb068_alpha_dummy_437;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0444) 0))))
                              (show (nb068_alpha_dummy_431 f) ≠ (nb068_alpha_dummy_438 f) from
                                (by
                                  unfold nb068_alpha_dummy_438;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0445 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_429) ≠ (nb068_alpha_dummy_441) from (by
                                unfold nb068_alpha_dummy_441;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0450) 0))))
                            (show (nb068_alpha_dummy_432 f) ≠ (nb068_alpha_dummy_442 f) from (by
                                unfold nb068_alpha_dummy_442;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0451 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_429) ≠ (nb068_alpha_dummy_437) from (by
                                  unfold nb068_alpha_dummy_437;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0448) 0))))
                              (show (nb068_alpha_dummy_432 f) ≠ (nb068_alpha_dummy_438 f) from
                                (by
                                  unfold nb068_alpha_dummy_438;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0449 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_429) ≠ (nb068_alpha_dummy_441) from (by
                                unfold nb068_alpha_dummy_441;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0450) 0))))
                            (show (nb068_alpha_dummy_432 f) ≠ (nb068_alpha_dummy_442 f) from (by
                                unfold nb068_alpha_dummy_442;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0451 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_429) ≠ (nb068_alpha_dummy_437) from (by
                                  unfold nb068_alpha_dummy_437;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0448) 0))))
                              (show (nb068_alpha_dummy_432 f) ≠ (nb068_alpha_dummy_438 f) from
                                (by
                                  unfold nb068_alpha_dummy_438;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0449 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0153 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)),
        ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)),
        ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)),
        ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)),
        ((nb068_alpha_dummy_419), (nb068_alpha_dummy_420 f)),
        ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)),
        ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_421))
          (Class.cv (nb068_alpha_dummy_414))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_422))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_421)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_421)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_421))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_423 f))
          (Class.cv (nb068_alpha_dummy_416 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_424 f))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_423 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_423 f)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_423 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_414) ≠ (nb068_alpha_dummy_421) from (by
              unfold nb068_alpha_dummy_421;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0430) 0))))
          (show (nb068_alpha_dummy_416 f) ≠ (nb068_alpha_dummy_423 f) from (by
              unfold nb068_alpha_dummy_423;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0431 f) 0))))
          (TAlphaVar.there (show (nb068_alpha_dummy_414) ≠ (nb068_alpha_dummy_422) from (by
                unfold nb068_alpha_dummy_422;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0430) 1))))
            (show (nb068_alpha_dummy_416 f) ≠ (nb068_alpha_dummy_424 f) from (by
                unfold nb068_alpha_dummy_424;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0431 f) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_414))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_416 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068_alpha_dummy_421) ≠ (nb068_alpha_dummy_428) from (by
                                  unfold nb068_alpha_dummy_428;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0434) 1))))
                              (show (nb068_alpha_dummy_423 f) ≠ (nb068_alpha_dummy_431 f) from
                                (by
                                  unfold nb068_alpha_dummy_431;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0435 f) 1))))
                              (TAlphaVar.there
                                (show (nb068_alpha_dummy_421) ≠ (nb068_alpha_dummy_427) from (by
                                    unfold nb068_alpha_dummy_427;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0434) 0)))) (show
                                  (nb068_alpha_dummy_423 f) ≠ (nb068_alpha_dummy_430 f) from (by
                                    unfold nb068_alpha_dummy_430;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0435 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_421) ≠ (nb068_alpha_dummy_425) from
                                    (by
                                      unfold nb068_alpha_dummy_425;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0432)
                                              0)))) (show
                                    (nb068_alpha_dummy_423 f) ≠ (nb068_alpha_dummy_426 f) from
                                    (by
                                      unfold nb068_alpha_dummy_426;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0433 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb068_alpha_dummy_429), (nb068_alpha_dummy_432 f)),
                                  ((nb068_alpha_dummy_428), (nb068_alpha_dummy_431 f)),
                                  ((nb068_alpha_dummy_427), (nb068_alpha_dummy_430 f)),
                                  ((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)),
                                  ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)),
                                  ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)),
                                  ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)),
                                  ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)),
                                  ((nb068_alpha_dummy_419), (nb068_alpha_dummy_420 f)),
                                  ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)),
                                  ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
                                  ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
                                  ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
                                  ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                                  ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                                  ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                                  ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                                  ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                    (nb068_alpha_dummy_004 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068_split_alpha_0152 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068_alpha_dummy_421) ≠ (nb068_alpha_dummy_425) from (by
                          unfold nb068_alpha_dummy_425;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0432) 0))))
                      (show (nb068_alpha_dummy_423 f) ≠ (nb068_alpha_dummy_426 f) from (by
                          unfold nb068_alpha_dummy_426;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0433 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)),
                      ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)),
                      ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)),
                      ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)),
                      ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)),
                      ((nb068_alpha_dummy_419), (nb068_alpha_dummy_420 f)),
                      ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)),
                      ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
                      ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
                      ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
                      ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                      ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                      ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                      ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_421) ≠ (nb068_alpha_dummy_425) from
                      (by
                        unfold nb068_alpha_dummy_425;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0432) 0))))
                    (show (nb068_alpha_dummy_423 f) ≠ (nb068_alpha_dummy_426 f) from (by
                        unfold nb068_alpha_dummy_426;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0433 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_421) ≠ (nb068_alpha_dummy_425) from (by
                          unfold nb068_alpha_dummy_425;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0432) 0))))
                      (show (nb068_alpha_dummy_423 f) ≠ (nb068_alpha_dummy_426 f) from (by
                          unfold nb068_alpha_dummy_426;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0433 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)),
                      ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)),
                      ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)),
                      ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)),
                      ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)),
                      ((nb068_alpha_dummy_419), (nb068_alpha_dummy_420 f)),
                      ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)),
                      ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
                      ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
                      ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
                      ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                      ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                      ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                      ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part054`. -/


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
noncomputable def nb068_split_alpha_0154 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_429), (nb068_alpha_dummy_432 f)),
        ((nb068_alpha_dummy_428), (nb068_alpha_dummy_431 f)),
        ((nb068_alpha_dummy_427), (nb068_alpha_dummy_430 f)),
        ((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)),
        ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)),
        ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)),
        ((nb068_alpha_dummy_447), (nb068_alpha_dummy_448 f)),
        ((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)),
        ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)),
        ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)),
        ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)),
        ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)),
        ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_428)) (Class.cv (nb068_alpha_dummy_429)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_427))
            (syn_cun (Class.cv (nb068_alpha_dummy_428)) (Class.cv (nb068_alpha_dummy_429))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_431 f))
            (Class.cv (nb068_alpha_dummy_432 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_430 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_431 f))
              (Class.cv (nb068_alpha_dummy_432 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_428) ≠ (nb068_alpha_dummy_435) from (by
                              unfold nb068_alpha_dummy_435;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0438) 0))))
                          (show (nb068_alpha_dummy_431 f) ≠ (nb068_alpha_dummy_436 f) from (by
                              unfold nb068_alpha_dummy_436;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0439 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_428) ≠ (nb068_alpha_dummy_433) from (by
                                unfold nb068_alpha_dummy_433;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0436) 0))))
                            (show (nb068_alpha_dummy_431 f) ≠ (nb068_alpha_dummy_434 f) from (by
                                unfold nb068_alpha_dummy_434;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0437 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_429) ≠ (nb068_alpha_dummy_435) from (by
                              unfold nb068_alpha_dummy_435;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0442) 0))))
                          (show (nb068_alpha_dummy_432 f) ≠ (nb068_alpha_dummy_436 f) from (by
                              unfold nb068_alpha_dummy_436;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0443 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_429) ≠ (nb068_alpha_dummy_433) from (by
                                unfold nb068_alpha_dummy_433;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0440) 0))))
                            (show (nb068_alpha_dummy_432 f) ≠ (nb068_alpha_dummy_434 f) from (by
                                unfold nb068_alpha_dummy_434;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0441 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_428) ≠ (nb068_alpha_dummy_435) from (by
                              unfold nb068_alpha_dummy_435;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0438) 0))))
                          (show (nb068_alpha_dummy_431 f) ≠ (nb068_alpha_dummy_436 f) from (by
                              unfold nb068_alpha_dummy_436;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0439 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_428) ≠ (nb068_alpha_dummy_433) from (by
                                unfold nb068_alpha_dummy_433;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0436) 0))))
                            (show (nb068_alpha_dummy_431 f) ≠ (nb068_alpha_dummy_434 f) from (by
                                unfold nb068_alpha_dummy_434;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0437 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_429) ≠ (nb068_alpha_dummy_435) from (by
                              unfold nb068_alpha_dummy_435;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0442) 0))))
                          (show (nb068_alpha_dummy_432 f) ≠ (nb068_alpha_dummy_436 f) from (by
                              unfold nb068_alpha_dummy_436;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0443 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_429) ≠ (nb068_alpha_dummy_433) from (by
                                unfold nb068_alpha_dummy_433;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0440) 0))))
                            (show (nb068_alpha_dummy_432 f) ≠ (nb068_alpha_dummy_434 f) from (by
                                unfold nb068_alpha_dummy_434;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0441 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_429), (nb068_alpha_dummy_432 f)),
          ((nb068_alpha_dummy_428), (nb068_alpha_dummy_431 f)),
          ((nb068_alpha_dummy_427), (nb068_alpha_dummy_430 f)),
          ((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)),
          ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)),
          ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)),
          ((nb068_alpha_dummy_447), (nb068_alpha_dummy_448 f)),
          ((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)),
          ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)),
          ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)),
          ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)),
          ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)),
          ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
          ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
          ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
          ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_428) ≠ (nb068_alpha_dummy_439) from (by
                                unfold nb068_alpha_dummy_439;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0446) 0))))
                            (show (nb068_alpha_dummy_431 f) ≠ (nb068_alpha_dummy_440 f) from (by
                                unfold nb068_alpha_dummy_440;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0447 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_428) ≠ (nb068_alpha_dummy_437) from (by
                                  unfold nb068_alpha_dummy_437;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0444) 0))))
                              (show (nb068_alpha_dummy_431 f) ≠ (nb068_alpha_dummy_438 f) from
                                (by
                                  unfold nb068_alpha_dummy_438;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0445 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_428) ≠ (nb068_alpha_dummy_439) from (by
                                unfold nb068_alpha_dummy_439;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0446) 0))))
                            (show (nb068_alpha_dummy_431 f) ≠ (nb068_alpha_dummy_440 f) from (by
                                unfold nb068_alpha_dummy_440;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0447 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_428) ≠ (nb068_alpha_dummy_437) from (by
                                  unfold nb068_alpha_dummy_437;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0444) 0))))
                              (show (nb068_alpha_dummy_431 f) ≠ (nb068_alpha_dummy_438 f) from
                                (by
                                  unfold nb068_alpha_dummy_438;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0445 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_429) ≠ (nb068_alpha_dummy_441) from (by
                                unfold nb068_alpha_dummy_441;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0450) 0))))
                            (show (nb068_alpha_dummy_432 f) ≠ (nb068_alpha_dummy_442 f) from (by
                                unfold nb068_alpha_dummy_442;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0451 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_429) ≠ (nb068_alpha_dummy_437) from (by
                                  unfold nb068_alpha_dummy_437;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0448) 0))))
                              (show (nb068_alpha_dummy_432 f) ≠ (nb068_alpha_dummy_438 f) from
                                (by
                                  unfold nb068_alpha_dummy_438;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0449 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_429) ≠ (nb068_alpha_dummy_441) from (by
                                unfold nb068_alpha_dummy_441;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0450) 0))))
                            (show (nb068_alpha_dummy_432 f) ≠ (nb068_alpha_dummy_442 f) from (by
                                unfold nb068_alpha_dummy_442;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0451 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_429) ≠ (nb068_alpha_dummy_437) from (by
                                  unfold nb068_alpha_dummy_437;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0448) 0))))
                              (show (nb068_alpha_dummy_432 f) ≠ (nb068_alpha_dummy_438 f) from
                                (by
                                  unfold nb068_alpha_dummy_438;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0449 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0155 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)),
        ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)),
        ((nb068_alpha_dummy_447), (nb068_alpha_dummy_448 f)),
        ((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)),
        ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)),
        ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)),
        ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)),
        ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)),
        ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.classEq (Class.cv (nb068_alpha_dummy_422))
        (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_421)) (syn_cnnc))
          (syn_cplc (Class.cv (nb068_alpha_dummy_421)) (syn_c1c))
          (Class.cv (nb068_alpha_dummy_421))))
      (Wff.classEq (Class.cv (nb068_alpha_dummy_424 f))
        (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_423 f)) (syn_cnnc))
          (syn_cplc (Class.cv (nb068_alpha_dummy_423 f)) (syn_c1c))
          (Class.cv (nb068_alpha_dummy_423 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068_alpha_dummy_414))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb068_alpha_dummy_416 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_421) ≠ (nb068_alpha_dummy_428) from (by
                              unfold nb068_alpha_dummy_428;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0434) 1))))
                          (show (nb068_alpha_dummy_423 f) ≠ (nb068_alpha_dummy_431 f) from (by
                              unfold nb068_alpha_dummy_431;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0435 f) 1))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_421) ≠ (nb068_alpha_dummy_427) from (by
                                unfold nb068_alpha_dummy_427;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0434) 0))))
                            (show (nb068_alpha_dummy_423 f) ≠ (nb068_alpha_dummy_430 f) from (by
                                unfold nb068_alpha_dummy_430;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0435 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_421) ≠ (nb068_alpha_dummy_425) from (by
                                  unfold nb068_alpha_dummy_425;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0432) 0))))
                              (show (nb068_alpha_dummy_423 f) ≠ (nb068_alpha_dummy_426 f) from
                                (by
                                  unfold nb068_alpha_dummy_426;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0433 f) 0))))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.refl_of_closed
                            [((nb068_alpha_dummy_429), (nb068_alpha_dummy_432 f)),
                              ((nb068_alpha_dummy_428), (nb068_alpha_dummy_431 f)),
                              ((nb068_alpha_dummy_427), (nb068_alpha_dummy_430 f)),
                              ((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)),
                              ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)),
                              ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)),
                              ((nb068_alpha_dummy_447), (nb068_alpha_dummy_448 f)),
                              ((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)),
                              ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)),
                              ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)),
                              ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)),
                              ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)),
                              ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
                              ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
                              ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
                              ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                              ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                              ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                              ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                              ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                              ((nb068_alpha_dummy_001), x),
                              ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                            (syn_c1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb068_split_alpha_0154 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb068_alpha_dummy_421) ≠ (nb068_alpha_dummy_425) from (by
                      unfold nb068_alpha_dummy_425;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0432) 0))))
                  (show (nb068_alpha_dummy_423 f) ≠ (nb068_alpha_dummy_426 f) from (by
                      unfold nb068_alpha_dummy_426;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0433 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                [((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)),
                  ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)),
                  ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)),
                  ((nb068_alpha_dummy_447), (nb068_alpha_dummy_448 f)),
                  ((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)),
                  ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)),
                  ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)),
                  ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)),
                  ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)),
                  ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
                  ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
                  ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
                  ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                  ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                  ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                  ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                  ((nb068_alpha_dummy_001), x),
                  ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068_alpha_dummy_421) ≠ (nb068_alpha_dummy_425) from (by
                    unfold nb068_alpha_dummy_425;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0432) 0))))
                (show (nb068_alpha_dummy_423 f) ≠ (nb068_alpha_dummy_426 f) from (by
                    unfold nb068_alpha_dummy_426;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0433 f) 0))))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (show (nb068_alpha_dummy_421) ≠ (nb068_alpha_dummy_425) from
                    (by
                      unfold nb068_alpha_dummy_425;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0432) 0))))
                  (show (nb068_alpha_dummy_423 f) ≠ (nb068_alpha_dummy_426 f) from (by
                      unfold nb068_alpha_dummy_426;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0433 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                [((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)),
                  ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)),
                  ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)),
                  ((nb068_alpha_dummy_447), (nb068_alpha_dummy_448 f)),
                  ((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)),
                  ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)),
                  ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)),
                  ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)),
                  ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)),
                  ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
                  ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
                  ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
                  ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                  ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                  ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                  ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                  ((nb068_alpha_dummy_001), x),
                  ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))

@[expose]
noncomputable def nb068_split_alpha_0156 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)),
        ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)),
        ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_443))
          (Class.cab (nb068_alpha_dummy_413)
            (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_443))
            (Class.cab (nb068_alpha_dummy_413)
              (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_444 f))
          (Class.cab (nb068_alpha_dummy_415 f)
            (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_444 f))
            (Class.cab (nb068_alpha_dummy_415 f)
              (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_414) from
                    (by
                      unfold nb068_alpha_dummy_414;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0452) 1))))
                  (show (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_416 f) from (by
                      unfold nb068_alpha_dummy_416;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0454 f) 1))))
                  (TAlphaVar.there (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_413) from
                      (by
                        unfold nb068_alpha_dummy_413;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0452) 0))))
                    (show (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_415 f) from (by
                        unfold nb068_alpha_dummy_415;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0454 f) 0)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_443) from (by
                          unfold nb068_alpha_dummy_443;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0456) 0))))
                      (show (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_444 f) from (by
                          unfold nb068_alpha_dummy_444;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0457 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_417) from (by
                            unfold nb068_alpha_dummy_417;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0453) 0))))
                        (show (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_418 f) from (by
                            unfold nb068_alpha_dummy_418;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0455 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_407))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_408))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_410 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb068_alpha_dummy_414) ≠
        (nb068_alpha_dummy_421) from (by
          unfold nb068_alpha_dummy_421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0430) 0)))) (show (nb068_alpha_dummy_416 f) ≠
        (nb068_alpha_dummy_423 f) from (by
          unfold nb068_alpha_dummy_423;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0431 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_414) ≠ (nb068_alpha_dummy_422) from (by
          unfold nb068_alpha_dummy_422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0430) 1)))) (show (nb068_alpha_dummy_416 f) ≠
        (nb068_alpha_dummy_424 f) from (by
          unfold nb068_alpha_dummy_424;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0431 f) 1)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_414) ≠ (nb068_alpha_dummy_447) from (by
          unfold nb068_alpha_dummy_447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0460) 0)))) (show (nb068_alpha_dummy_416 f) ≠
        (nb068_alpha_dummy_448 f) from (by
          unfold nb068_alpha_dummy_448;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0461 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_414) ≠ (nb068_alpha_dummy_445) from (by
          unfold nb068_alpha_dummy_445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0458) 0)))) (show (nb068_alpha_dummy_416 f) ≠
        (nb068_alpha_dummy_446 f) from (by
          unfold nb068_alpha_dummy_446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0459 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068_split_alpha_0155 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb068_alpha_dummy_414) ≠
        (nb068_alpha_dummy_421) from (by
          unfold nb068_alpha_dummy_421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0430) 0)))) (show (nb068_alpha_dummy_416 f) ≠
        (nb068_alpha_dummy_423 f) from (by
          unfold nb068_alpha_dummy_423;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0431 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_414) ≠ (nb068_alpha_dummy_422) from (by
          unfold nb068_alpha_dummy_422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0430) 1)))) (show (nb068_alpha_dummy_416 f) ≠
        (nb068_alpha_dummy_424 f) from (by
          unfold nb068_alpha_dummy_424;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0431 f) 1)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_414) ≠ (nb068_alpha_dummy_447) from (by
          unfold nb068_alpha_dummy_447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0460) 0)))) (show (nb068_alpha_dummy_416 f) ≠
        (nb068_alpha_dummy_448 f) from (by
          unfold nb068_alpha_dummy_448;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0461 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_414) ≠ (nb068_alpha_dummy_445) from (by
          unfold nb068_alpha_dummy_445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0458) 0)))) (show (nb068_alpha_dummy_416 f) ≠
        (nb068_alpha_dummy_446 f) from (by
          unfold nb068_alpha_dummy_446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0459 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068_split_alpha_0155 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)),
                          ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)),
                          ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)),
                          ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)),
                          ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)),
                          ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
                          ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
                          ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
                          ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_414) from
                      (by
                        unfold nb068_alpha_dummy_414;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0452) 1))))
                    (show (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_416 f) from (by
                        unfold nb068_alpha_dummy_416;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0454 f) 1)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_413) from (by
                          unfold nb068_alpha_dummy_413;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0452) 0))))
                      (show (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_415 f) from (by
                          unfold nb068_alpha_dummy_415;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0454 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_443) from (by
                            unfold nb068_alpha_dummy_443;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0456) 0))))
                        (show (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_444 f) from (by
                            unfold nb068_alpha_dummy_444;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0457 f) 0))))
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_417) from (by
                              unfold nb068_alpha_dummy_417;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0453) 0))))
                          (show (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_418 f) from (by
                              unfold nb068_alpha_dummy_418;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0455 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068_alpha_dummy_407))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_408))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_410 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_414) ≠ (nb068_alpha_dummy_421) from (by
          unfold nb068_alpha_dummy_421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0430) 0)))) (show (nb068_alpha_dummy_416 f) ≠
        (nb068_alpha_dummy_423 f) from (by
          unfold nb068_alpha_dummy_423;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0431 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_414) ≠ (nb068_alpha_dummy_422) from (by
          unfold nb068_alpha_dummy_422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0430) 1)))) (show (nb068_alpha_dummy_416 f) ≠
        (nb068_alpha_dummy_424 f) from (by
          unfold nb068_alpha_dummy_424;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0431 f) 1)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_414) ≠ (nb068_alpha_dummy_447) from (by
          unfold nb068_alpha_dummy_447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0460) 0)))) (show (nb068_alpha_dummy_416 f) ≠
        (nb068_alpha_dummy_448 f) from (by
          unfold nb068_alpha_dummy_448;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0461 f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_414) ≠ (nb068_alpha_dummy_445)
        from (by
          unfold nb068_alpha_dummy_445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0458)
                  0)))) (show (nb068_alpha_dummy_416 f) ≠ (nb068_alpha_dummy_446 f) from (by
          unfold nb068_alpha_dummy_446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0459 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068_split_alpha_0155 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_414) ≠ (nb068_alpha_dummy_421) from (by
          unfold nb068_alpha_dummy_421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0430) 0)))) (show (nb068_alpha_dummy_416 f) ≠
        (nb068_alpha_dummy_423 f) from (by
          unfold nb068_alpha_dummy_423;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0431 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_414) ≠ (nb068_alpha_dummy_422) from (by
          unfold nb068_alpha_dummy_422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0430) 1)))) (show (nb068_alpha_dummy_416 f) ≠
        (nb068_alpha_dummy_424 f) from (by
          unfold nb068_alpha_dummy_424;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0431 f) 1)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_414) ≠ (nb068_alpha_dummy_447) from (by
          unfold nb068_alpha_dummy_447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0460) 0)))) (show (nb068_alpha_dummy_416 f) ≠
        (nb068_alpha_dummy_448 f) from (by
          unfold nb068_alpha_dummy_448;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0461 f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_414) ≠ (nb068_alpha_dummy_445)
        from (by
          unfold nb068_alpha_dummy_445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0458)
                  0)))) (show (nb068_alpha_dummy_416 f) ≠ (nb068_alpha_dummy_446 f) from (by
          unfold nb068_alpha_dummy_446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0459 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068_split_alpha_0155 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)),
                            ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)),
                            ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)),
                            ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)),
                            ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)),
                            ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
                            ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
                            ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
                            ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                            ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                            ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                            ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                            ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                            ((nb068_alpha_dummy_001), x),
                            ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0157 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_465), (nb068_alpha_dummy_468 f)),
        ((nb068_alpha_dummy_464), (nb068_alpha_dummy_467 f)),
        ((nb068_alpha_dummy_463), (nb068_alpha_dummy_466 f)),
        ((nb068_alpha_dummy_461), (nb068_alpha_dummy_462 f)),
        ((nb068_alpha_dummy_457), (nb068_alpha_dummy_459 f)),
        ((nb068_alpha_dummy_458), (nb068_alpha_dummy_460 f)),
        ((nb068_alpha_dummy_450), (nb068_alpha_dummy_452 f)),
        ((nb068_alpha_dummy_449), (nb068_alpha_dummy_451 f)),
        ((nb068_alpha_dummy_455), (nb068_alpha_dummy_456 f)),
        ((nb068_alpha_dummy_453), (nb068_alpha_dummy_454 f)),
        ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_464)) (Class.cv (nb068_alpha_dummy_465)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_463))
            (syn_cun (Class.cv (nb068_alpha_dummy_464)) (Class.cv (nb068_alpha_dummy_465))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_467 f))
            (Class.cv (nb068_alpha_dummy_468 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_466 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_467 f))
              (Class.cv (nb068_alpha_dummy_468 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_464) ≠ (nb068_alpha_dummy_471) from (by
                              unfold nb068_alpha_dummy_471;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0476) 0))))
                          (show (nb068_alpha_dummy_467 f) ≠ (nb068_alpha_dummy_472 f) from (by
                              unfold nb068_alpha_dummy_472;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0477 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_464) ≠ (nb068_alpha_dummy_469) from (by
                                unfold nb068_alpha_dummy_469;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0474) 0))))
                            (show (nb068_alpha_dummy_467 f) ≠ (nb068_alpha_dummy_470 f) from (by
                                unfold nb068_alpha_dummy_470;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0475 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_465) ≠ (nb068_alpha_dummy_471) from (by
                              unfold nb068_alpha_dummy_471;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0480) 0))))
                          (show (nb068_alpha_dummy_468 f) ≠ (nb068_alpha_dummy_472 f) from (by
                              unfold nb068_alpha_dummy_472;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0481 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_465) ≠ (nb068_alpha_dummy_469) from (by
                                unfold nb068_alpha_dummy_469;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0478) 0))))
                            (show (nb068_alpha_dummy_468 f) ≠ (nb068_alpha_dummy_470 f) from (by
                                unfold nb068_alpha_dummy_470;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0479 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_464) ≠ (nb068_alpha_dummy_471) from (by
                              unfold nb068_alpha_dummy_471;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0476) 0))))
                          (show (nb068_alpha_dummy_467 f) ≠ (nb068_alpha_dummy_472 f) from (by
                              unfold nb068_alpha_dummy_472;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0477 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_464) ≠ (nb068_alpha_dummy_469) from (by
                                unfold nb068_alpha_dummy_469;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0474) 0))))
                            (show (nb068_alpha_dummy_467 f) ≠ (nb068_alpha_dummy_470 f) from (by
                                unfold nb068_alpha_dummy_470;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0475 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_465) ≠ (nb068_alpha_dummy_471) from (by
                              unfold nb068_alpha_dummy_471;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0480) 0))))
                          (show (nb068_alpha_dummy_468 f) ≠ (nb068_alpha_dummy_472 f) from (by
                              unfold nb068_alpha_dummy_472;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0481 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_465) ≠ (nb068_alpha_dummy_469) from (by
                                unfold nb068_alpha_dummy_469;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0478) 0))))
                            (show (nb068_alpha_dummy_468 f) ≠ (nb068_alpha_dummy_470 f) from (by
                                unfold nb068_alpha_dummy_470;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0479 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_465), (nb068_alpha_dummy_468 f)),
          ((nb068_alpha_dummy_464), (nb068_alpha_dummy_467 f)),
          ((nb068_alpha_dummy_463), (nb068_alpha_dummy_466 f)),
          ((nb068_alpha_dummy_461), (nb068_alpha_dummy_462 f)),
          ((nb068_alpha_dummy_457), (nb068_alpha_dummy_459 f)),
          ((nb068_alpha_dummy_458), (nb068_alpha_dummy_460 f)),
          ((nb068_alpha_dummy_450), (nb068_alpha_dummy_452 f)),
          ((nb068_alpha_dummy_449), (nb068_alpha_dummy_451 f)),
          ((nb068_alpha_dummy_455), (nb068_alpha_dummy_456 f)),
          ((nb068_alpha_dummy_453), (nb068_alpha_dummy_454 f)),
          ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
          ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
          ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
          ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_464) ≠ (nb068_alpha_dummy_475) from (by
                                unfold nb068_alpha_dummy_475;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0484) 0))))
                            (show (nb068_alpha_dummy_467 f) ≠ (nb068_alpha_dummy_476 f) from (by
                                unfold nb068_alpha_dummy_476;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0485 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_464) ≠ (nb068_alpha_dummy_473) from (by
                                  unfold nb068_alpha_dummy_473;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0482) 0))))
                              (show (nb068_alpha_dummy_467 f) ≠ (nb068_alpha_dummy_474 f) from
                                (by
                                  unfold nb068_alpha_dummy_474;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0483 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_464) ≠ (nb068_alpha_dummy_475) from (by
                                unfold nb068_alpha_dummy_475;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0484) 0))))
                            (show (nb068_alpha_dummy_467 f) ≠ (nb068_alpha_dummy_476 f) from (by
                                unfold nb068_alpha_dummy_476;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0485 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_464) ≠ (nb068_alpha_dummy_473) from (by
                                  unfold nb068_alpha_dummy_473;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0482) 0))))
                              (show (nb068_alpha_dummy_467 f) ≠ (nb068_alpha_dummy_474 f) from
                                (by
                                  unfold nb068_alpha_dummy_474;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0483 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_465) ≠ (nb068_alpha_dummy_477) from (by
                                unfold nb068_alpha_dummy_477;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0488) 0))))
                            (show (nb068_alpha_dummy_468 f) ≠ (nb068_alpha_dummy_478 f) from (by
                                unfold nb068_alpha_dummy_478;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0489 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_465) ≠ (nb068_alpha_dummy_473) from (by
                                  unfold nb068_alpha_dummy_473;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0486) 0))))
                              (show (nb068_alpha_dummy_468 f) ≠ (nb068_alpha_dummy_474 f) from
                                (by
                                  unfold nb068_alpha_dummy_474;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0487 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_465) ≠ (nb068_alpha_dummy_477) from (by
                                unfold nb068_alpha_dummy_477;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0488) 0))))
                            (show (nb068_alpha_dummy_468 f) ≠ (nb068_alpha_dummy_478 f) from (by
                                unfold nb068_alpha_dummy_478;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0489 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_465) ≠ (nb068_alpha_dummy_473) from (by
                                  unfold nb068_alpha_dummy_473;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0486) 0))))
                              (show (nb068_alpha_dummy_468 f) ≠ (nb068_alpha_dummy_474 f) from
                                (by
                                  unfold nb068_alpha_dummy_474;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0487 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
