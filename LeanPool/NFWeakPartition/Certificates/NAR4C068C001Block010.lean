/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C068C001Part036

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C068C001Part037`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0089`. -/
@[expose]
noncomputable def nb068SplitAlpha0089 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy351), (nb068AlphaDummy354 f)),
        ((nb068AlphaDummy350), (nb068AlphaDummy353 f)),
        ((nb068AlphaDummy349), (nb068AlphaDummy352 f)),
        ((nb068AlphaDummy347), (nb068AlphaDummy348 f)),
        ((nb068AlphaDummy343), (nb068AlphaDummy345 f)),
        ((nb068AlphaDummy344), (nb068AlphaDummy346 f)),
        ((nb068AlphaDummy336), (nb068AlphaDummy338 f)),
        ((nb068AlphaDummy335), (nb068AlphaDummy337 f)),
        ((nb068AlphaDummy341), (nb068AlphaDummy342 f)),
        ((nb068AlphaDummy339), (nb068AlphaDummy340 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy350)) (Class.cv (nb068AlphaDummy351)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy349))
            (synCun (Class.cv (nb068AlphaDummy350)) (Class.cv (nb068AlphaDummy351))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy353 f))
            (Class.cv (nb068AlphaDummy354 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy352 f))
            (synCun (Class.cv (nb068AlphaDummy353 f))
              (Class.cv (nb068AlphaDummy354 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy350) ≠ (nb068AlphaDummy357) from (by
                              unfold nb068AlphaDummy357;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0358) 0))))
                          (show (nb068AlphaDummy353 f) ≠ (nb068AlphaDummy358 f) from (by
                              unfold nb068AlphaDummy358;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0359 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy350) ≠ (nb068AlphaDummy355) from (by
                                unfold nb068AlphaDummy355;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0356) 0))))
                            (show (nb068AlphaDummy353 f) ≠ (nb068AlphaDummy356 f) from (by
                                unfold nb068AlphaDummy356;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0357 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy351) ≠ (nb068AlphaDummy357) from (by
                              unfold nb068AlphaDummy357;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0362) 0))))
                          (show (nb068AlphaDummy354 f) ≠ (nb068AlphaDummy358 f) from (by
                              unfold nb068AlphaDummy358;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0363 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy351) ≠ (nb068AlphaDummy355) from (by
                                unfold nb068AlphaDummy355;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0360) 0))))
                            (show (nb068AlphaDummy354 f) ≠ (nb068AlphaDummy356 f) from (by
                                unfold nb068AlphaDummy356;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0361 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy350) ≠ (nb068AlphaDummy357) from (by
                              unfold nb068AlphaDummy357;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0358) 0))))
                          (show (nb068AlphaDummy353 f) ≠ (nb068AlphaDummy358 f) from (by
                              unfold nb068AlphaDummy358;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0359 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy350) ≠ (nb068AlphaDummy355) from (by
                                unfold nb068AlphaDummy355;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0356) 0))))
                            (show (nb068AlphaDummy353 f) ≠ (nb068AlphaDummy356 f) from (by
                                unfold nb068AlphaDummy356;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0357 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy351) ≠ (nb068AlphaDummy357) from (by
                              unfold nb068AlphaDummy357;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0362) 0))))
                          (show (nb068AlphaDummy354 f) ≠ (nb068AlphaDummy358 f) from (by
                              unfold nb068AlphaDummy358;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0363 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy351) ≠ (nb068AlphaDummy355) from (by
                                unfold nb068AlphaDummy355;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0360) 0))))
                            (show (nb068AlphaDummy354 f) ≠ (nb068AlphaDummy356 f) from (by
                                unfold nb068AlphaDummy356;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0361 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy351), (nb068AlphaDummy354 f)),
          ((nb068AlphaDummy350), (nb068AlphaDummy353 f)),
          ((nb068AlphaDummy349), (nb068AlphaDummy352 f)),
          ((nb068AlphaDummy347), (nb068AlphaDummy348 f)),
          ((nb068AlphaDummy343), (nb068AlphaDummy345 f)),
          ((nb068AlphaDummy344), (nb068AlphaDummy346 f)),
          ((nb068AlphaDummy336), (nb068AlphaDummy338 f)),
          ((nb068AlphaDummy335), (nb068AlphaDummy337 f)),
          ((nb068AlphaDummy341), (nb068AlphaDummy342 f)),
          ((nb068AlphaDummy339), (nb068AlphaDummy340 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
          ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy350) ≠ (nb068AlphaDummy361) from (by
                                unfold nb068AlphaDummy361;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0366) 0))))
                            (show (nb068AlphaDummy353 f) ≠ (nb068AlphaDummy362 f) from (by
                                unfold nb068AlphaDummy362;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0367 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy350) ≠ (nb068AlphaDummy359) from (by
                                  unfold nb068AlphaDummy359;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0364) 0))))
                              (show (nb068AlphaDummy353 f) ≠ (nb068AlphaDummy360 f) from
                                (by
                                  unfold nb068AlphaDummy360;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0365 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy350) ≠ (nb068AlphaDummy361) from (by
                                unfold nb068AlphaDummy361;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0366) 0))))
                            (show (nb068AlphaDummy353 f) ≠ (nb068AlphaDummy362 f) from (by
                                unfold nb068AlphaDummy362;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0367 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy350) ≠ (nb068AlphaDummy359) from (by
                                  unfold nb068AlphaDummy359;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0364) 0))))
                              (show (nb068AlphaDummy353 f) ≠ (nb068AlphaDummy360 f) from
                                (by
                                  unfold nb068AlphaDummy360;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0365 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy351) ≠ (nb068AlphaDummy363) from (by
                                unfold nb068AlphaDummy363;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0370) 0))))
                            (show (nb068AlphaDummy354 f) ≠ (nb068AlphaDummy364 f) from (by
                                unfold nb068AlphaDummy364;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0371 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy351) ≠ (nb068AlphaDummy359) from (by
                                  unfold nb068AlphaDummy359;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0368) 0))))
                              (show (nb068AlphaDummy354 f) ≠ (nb068AlphaDummy360 f) from
                                (by
                                  unfold nb068AlphaDummy360;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0369 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy351) ≠ (nb068AlphaDummy363) from (by
                                unfold nb068AlphaDummy363;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0370) 0))))
                            (show (nb068AlphaDummy354 f) ≠ (nb068AlphaDummy364 f) from (by
                                unfold nb068AlphaDummy364;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0371 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy351) ≠ (nb068AlphaDummy359) from (by
                                  unfold nb068AlphaDummy359;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0368) 0))))
                              (show (nb068AlphaDummy354 f) ≠ (nb068AlphaDummy360 f) from
                                (by
                                  unfold nb068AlphaDummy360;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0369 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0090`. -/
@[expose]
noncomputable def nb068SplitAlpha0090 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy343), (nb068AlphaDummy345 f)),
        ((nb068AlphaDummy344), (nb068AlphaDummy346 f)),
        ((nb068AlphaDummy336), (nb068AlphaDummy338 f)),
        ((nb068AlphaDummy335), (nb068AlphaDummy337 f)),
        ((nb068AlphaDummy341), (nb068AlphaDummy342 f)),
        ((nb068AlphaDummy339), (nb068AlphaDummy340 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy343))
            (Class.cv (nb068AlphaDummy336))) (Wff.classEq (Class.cv (nb068AlphaDummy344))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy343)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy343)) (synC1c))
              (Class.cv (nb068AlphaDummy343))))))
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy345 f))
            (Class.cv (nb068AlphaDummy338 f)))
          (Wff.classEq (Class.cv (nb068AlphaDummy346 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy345 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy345 f)) (synC1c))
              (Class.cv (nb068AlphaDummy345 f)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb068AlphaDummy336) ≠ (nb068AlphaDummy343) from (by
                unfold nb068AlphaDummy343;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0350) 0))))
            (show (nb068AlphaDummy338 f) ≠ (nb068AlphaDummy345 f) from (by
                unfold nb068AlphaDummy345;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0351 f) 0))))
            (TAlphaVar.there (show (nb068AlphaDummy336) ≠ (nb068AlphaDummy344) from (by
                  unfold nb068AlphaDummy344;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0350) 1))))
              (show (nb068AlphaDummy338 f) ≠ (nb068AlphaDummy346 f) from (by
                  unfold nb068AlphaDummy346;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0351 f) 1))))
              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy336))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068AlphaDummy338 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy343) ≠ (nb068AlphaDummy350) from (by
                                  unfold nb068AlphaDummy350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0354) 1))))
                              (show (nb068AlphaDummy345 f) ≠ (nb068AlphaDummy353 f) from
                                (by
                                  unfold nb068AlphaDummy353;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0355 f) 1))))
                              (TAlphaVar.there
                                (show (nb068AlphaDummy343) ≠ (nb068AlphaDummy349) from (by
                                    unfold nb068AlphaDummy349;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0354) 0)))) (show
                                  (nb068AlphaDummy345 f) ≠ (nb068AlphaDummy352 f) from (by
                                    unfold nb068AlphaDummy352;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0355 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy343) ≠ (nb068AlphaDummy347) from
                                    (by
                                      unfold nb068AlphaDummy347;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0352)
                                              0)))) (show
                                    (nb068AlphaDummy345 f) ≠ (nb068AlphaDummy348 f) from
                                    (by
                                      unfold nb068AlphaDummy348;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0353 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy351), (nb068AlphaDummy354 f)),
                                  ((nb068AlphaDummy350), (nb068AlphaDummy353 f)),
                                  ((nb068AlphaDummy349), (nb068AlphaDummy352 f)),
                                  ((nb068AlphaDummy347), (nb068AlphaDummy348 f)),
                                  ((nb068AlphaDummy343), (nb068AlphaDummy345 f)),
                                  ((nb068AlphaDummy344), (nb068AlphaDummy346 f)),
                                  ((nb068AlphaDummy336), (nb068AlphaDummy338 f)),
                                  ((nb068AlphaDummy335), (nb068AlphaDummy337 f)),
                                  ((nb068AlphaDummy341), (nb068AlphaDummy342 f)),
                                  ((nb068AlphaDummy339), (nb068AlphaDummy340 f)),
                                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                                  ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                                  ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0089 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068AlphaDummy343) ≠ (nb068AlphaDummy347) from (by
                          unfold nb068AlphaDummy347;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0352) 0))))
                      (show (nb068AlphaDummy345 f) ≠ (nb068AlphaDummy348 f) from (by
                          unfold nb068AlphaDummy348;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0353 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy347), (nb068AlphaDummy348 f)),
                      ((nb068AlphaDummy343), (nb068AlphaDummy345 f)),
                      ((nb068AlphaDummy344), (nb068AlphaDummy346 f)),
                      ((nb068AlphaDummy336), (nb068AlphaDummy338 f)),
                      ((nb068AlphaDummy335), (nb068AlphaDummy337 f)),
                      ((nb068AlphaDummy341), (nb068AlphaDummy342 f)),
                      ((nb068AlphaDummy339), (nb068AlphaDummy340 f)),
                      ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                      ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                      ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                      ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                      ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy343) ≠ (nb068AlphaDummy347) from
                      (by
                        unfold nb068AlphaDummy347;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0352) 0))))
                    (show (nb068AlphaDummy345 f) ≠ (nb068AlphaDummy348 f) from (by
                        unfold nb068AlphaDummy348;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0353 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy343) ≠ (nb068AlphaDummy347) from (by
                          unfold nb068AlphaDummy347;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0352) 0))))
                      (show (nb068AlphaDummy345 f) ≠ (nb068AlphaDummy348 f) from (by
                          unfold nb068AlphaDummy348;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0353 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy347), (nb068AlphaDummy348 f)),
                      ((nb068AlphaDummy343), (nb068AlphaDummy345 f)),
                      ((nb068AlphaDummy344), (nb068AlphaDummy346 f)),
                      ((nb068AlphaDummy336), (nb068AlphaDummy338 f)),
                      ((nb068AlphaDummy335), (nb068AlphaDummy337 f)),
                      ((nb068AlphaDummy341), (nb068AlphaDummy342 f)),
                      ((nb068AlphaDummy339), (nb068AlphaDummy340 f)),
                      ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                      ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                      ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                      ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                      ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0091`. -/
@[expose]
noncomputable def nb068SplitAlpha0091 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy351), (nb068AlphaDummy354 f)),
        ((nb068AlphaDummy350), (nb068AlphaDummy353 f)),
        ((nb068AlphaDummy349), (nb068AlphaDummy352 f)),
        ((nb068AlphaDummy347), (nb068AlphaDummy348 f)),
        ((nb068AlphaDummy343), (nb068AlphaDummy345 f)),
        ((nb068AlphaDummy344), (nb068AlphaDummy346 f)),
        ((nb068AlphaDummy369), (nb068AlphaDummy370 f)),
        ((nb068AlphaDummy367), (nb068AlphaDummy368 f)),
        ((nb068AlphaDummy336), (nb068AlphaDummy338 f)),
        ((nb068AlphaDummy335), (nb068AlphaDummy337 f)),
        ((nb068AlphaDummy365), (nb068AlphaDummy366 f)),
        ((nb068AlphaDummy339), (nb068AlphaDummy340 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy350)) (Class.cv (nb068AlphaDummy351)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy349))
            (synCun (Class.cv (nb068AlphaDummy350)) (Class.cv (nb068AlphaDummy351))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy353 f))
            (Class.cv (nb068AlphaDummy354 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy352 f))
            (synCun (Class.cv (nb068AlphaDummy353 f))
              (Class.cv (nb068AlphaDummy354 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy350) ≠ (nb068AlphaDummy357) from (by
                              unfold nb068AlphaDummy357;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0358) 0))))
                          (show (nb068AlphaDummy353 f) ≠ (nb068AlphaDummy358 f) from (by
                              unfold nb068AlphaDummy358;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0359 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy350) ≠ (nb068AlphaDummy355) from (by
                                unfold nb068AlphaDummy355;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0356) 0))))
                            (show (nb068AlphaDummy353 f) ≠ (nb068AlphaDummy356 f) from (by
                                unfold nb068AlphaDummy356;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0357 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy351) ≠ (nb068AlphaDummy357) from (by
                              unfold nb068AlphaDummy357;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0362) 0))))
                          (show (nb068AlphaDummy354 f) ≠ (nb068AlphaDummy358 f) from (by
                              unfold nb068AlphaDummy358;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0363 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy351) ≠ (nb068AlphaDummy355) from (by
                                unfold nb068AlphaDummy355;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0360) 0))))
                            (show (nb068AlphaDummy354 f) ≠ (nb068AlphaDummy356 f) from (by
                                unfold nb068AlphaDummy356;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0361 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy350) ≠ (nb068AlphaDummy357) from (by
                              unfold nb068AlphaDummy357;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0358) 0))))
                          (show (nb068AlphaDummy353 f) ≠ (nb068AlphaDummy358 f) from (by
                              unfold nb068AlphaDummy358;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0359 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy350) ≠ (nb068AlphaDummy355) from (by
                                unfold nb068AlphaDummy355;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0356) 0))))
                            (show (nb068AlphaDummy353 f) ≠ (nb068AlphaDummy356 f) from (by
                                unfold nb068AlphaDummy356;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0357 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy351) ≠ (nb068AlphaDummy357) from (by
                              unfold nb068AlphaDummy357;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0362) 0))))
                          (show (nb068AlphaDummy354 f) ≠ (nb068AlphaDummy358 f) from (by
                              unfold nb068AlphaDummy358;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0363 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy351) ≠ (nb068AlphaDummy355) from (by
                                unfold nb068AlphaDummy355;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0360) 0))))
                            (show (nb068AlphaDummy354 f) ≠ (nb068AlphaDummy356 f) from (by
                                unfold nb068AlphaDummy356;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0361 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy351), (nb068AlphaDummy354 f)),
          ((nb068AlphaDummy350), (nb068AlphaDummy353 f)),
          ((nb068AlphaDummy349), (nb068AlphaDummy352 f)),
          ((nb068AlphaDummy347), (nb068AlphaDummy348 f)),
          ((nb068AlphaDummy343), (nb068AlphaDummy345 f)),
          ((nb068AlphaDummy344), (nb068AlphaDummy346 f)),
          ((nb068AlphaDummy369), (nb068AlphaDummy370 f)),
          ((nb068AlphaDummy367), (nb068AlphaDummy368 f)),
          ((nb068AlphaDummy336), (nb068AlphaDummy338 f)),
          ((nb068AlphaDummy335), (nb068AlphaDummy337 f)),
          ((nb068AlphaDummy365), (nb068AlphaDummy366 f)),
          ((nb068AlphaDummy339), (nb068AlphaDummy340 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
          ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy350) ≠ (nb068AlphaDummy361) from (by
                                unfold nb068AlphaDummy361;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0366) 0))))
                            (show (nb068AlphaDummy353 f) ≠ (nb068AlphaDummy362 f) from (by
                                unfold nb068AlphaDummy362;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0367 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy350) ≠ (nb068AlphaDummy359) from (by
                                  unfold nb068AlphaDummy359;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0364) 0))))
                              (show (nb068AlphaDummy353 f) ≠ (nb068AlphaDummy360 f) from
                                (by
                                  unfold nb068AlphaDummy360;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0365 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy350) ≠ (nb068AlphaDummy361) from (by
                                unfold nb068AlphaDummy361;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0366) 0))))
                            (show (nb068AlphaDummy353 f) ≠ (nb068AlphaDummy362 f) from (by
                                unfold nb068AlphaDummy362;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0367 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy350) ≠ (nb068AlphaDummy359) from (by
                                  unfold nb068AlphaDummy359;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0364) 0))))
                              (show (nb068AlphaDummy353 f) ≠ (nb068AlphaDummy360 f) from
                                (by
                                  unfold nb068AlphaDummy360;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0365 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy351) ≠ (nb068AlphaDummy363) from (by
                                unfold nb068AlphaDummy363;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0370) 0))))
                            (show (nb068AlphaDummy354 f) ≠ (nb068AlphaDummy364 f) from (by
                                unfold nb068AlphaDummy364;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0371 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy351) ≠ (nb068AlphaDummy359) from (by
                                  unfold nb068AlphaDummy359;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0368) 0))))
                              (show (nb068AlphaDummy354 f) ≠ (nb068AlphaDummy360 f) from
                                (by
                                  unfold nb068AlphaDummy360;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0369 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy351) ≠ (nb068AlphaDummy363) from (by
                                unfold nb068AlphaDummy363;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0370) 0))))
                            (show (nb068AlphaDummy354 f) ≠ (nb068AlphaDummy364 f) from (by
                                unfold nb068AlphaDummy364;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0371 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy351) ≠ (nb068AlphaDummy359) from (by
                                  unfold nb068AlphaDummy359;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0368) 0))))
                              (show (nb068AlphaDummy354 f) ≠ (nb068AlphaDummy360 f) from
                                (by
                                  unfold nb068AlphaDummy360;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0369 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part038`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0092`. -/
@[expose]
noncomputable def nb068SplitAlpha0092 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy343), (nb068AlphaDummy345 f)),
        ((nb068AlphaDummy344), (nb068AlphaDummy346 f)),
        ((nb068AlphaDummy369), (nb068AlphaDummy370 f)),
        ((nb068AlphaDummy367), (nb068AlphaDummy368 f)),
        ((nb068AlphaDummy336), (nb068AlphaDummy338 f)),
        ((nb068AlphaDummy335), (nb068AlphaDummy337 f)),
        ((nb068AlphaDummy365), (nb068AlphaDummy366 f)),
        ((nb068AlphaDummy339), (nb068AlphaDummy340 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy343))
          (Class.cv (nb068AlphaDummy336))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy344))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy343)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy343)) (synC1c))
              (Class.cv (nb068AlphaDummy343))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy345 f))
          (Class.cv (nb068AlphaDummy338 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy346 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy345 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy345 f)) (synC1c))
              (Class.cv (nb068AlphaDummy345 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy336) ≠ (nb068AlphaDummy343) from (by
              unfold nb068AlphaDummy343;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0350) 0))))
          (show (nb068AlphaDummy338 f) ≠ (nb068AlphaDummy345 f) from (by
              unfold nb068AlphaDummy345;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0351 f) 0))))
          (TAlphaVar.there (show (nb068AlphaDummy336) ≠ (nb068AlphaDummy344) from (by
                unfold nb068AlphaDummy344;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0350) 1))))
            (show (nb068AlphaDummy338 f) ≠ (nb068AlphaDummy346 f) from (by
                unfold nb068AlphaDummy346;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0351 f) 1))))
            (TAlphaVar.there (show (nb068AlphaDummy336) ≠ (nb068AlphaDummy369) from (by
                  unfold nb068AlphaDummy369;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0380) 0))))
              (show (nb068AlphaDummy338 f) ≠ (nb068AlphaDummy370 f) from (by
                  unfold nb068AlphaDummy370;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0381 f) 0))))
              (TAlphaVar.there (show (nb068AlphaDummy336) ≠ (nb068AlphaDummy367) from (by
                    unfold nb068AlphaDummy367;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0378) 0))))
                (show (nb068AlphaDummy338 f) ≠ (nb068AlphaDummy368 f) from (by
                    unfold nb068AlphaDummy368;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0379 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy336))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068AlphaDummy338 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy343) ≠ (nb068AlphaDummy350) from (by
                                  unfold nb068AlphaDummy350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0354) 1))))
                              (show (nb068AlphaDummy345 f) ≠ (nb068AlphaDummy353 f) from
                                (by
                                  unfold nb068AlphaDummy353;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0355 f) 1))))
                              (TAlphaVar.there
                                (show (nb068AlphaDummy343) ≠ (nb068AlphaDummy349) from (by
                                    unfold nb068AlphaDummy349;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0354) 0)))) (show
                                  (nb068AlphaDummy345 f) ≠ (nb068AlphaDummy352 f) from (by
                                    unfold nb068AlphaDummy352;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0355 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy343) ≠ (nb068AlphaDummy347) from
                                    (by
                                      unfold nb068AlphaDummy347;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0352)
                                              0)))) (show
                                    (nb068AlphaDummy345 f) ≠ (nb068AlphaDummy348 f) from
                                    (by
                                      unfold nb068AlphaDummy348;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0353 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy351), (nb068AlphaDummy354 f)),
                                  ((nb068AlphaDummy350), (nb068AlphaDummy353 f)),
                                  ((nb068AlphaDummy349), (nb068AlphaDummy352 f)),
                                  ((nb068AlphaDummy347), (nb068AlphaDummy348 f)),
                                  ((nb068AlphaDummy343), (nb068AlphaDummy345 f)),
                                  ((nb068AlphaDummy344), (nb068AlphaDummy346 f)),
                                  ((nb068AlphaDummy369), (nb068AlphaDummy370 f)),
                                  ((nb068AlphaDummy367), (nb068AlphaDummy368 f)),
                                  ((nb068AlphaDummy336), (nb068AlphaDummy338 f)),
                                  ((nb068AlphaDummy335), (nb068AlphaDummy337 f)),
                                  ((nb068AlphaDummy365), (nb068AlphaDummy366 f)),
                                  ((nb068AlphaDummy339), (nb068AlphaDummy340 f)),
                                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                                  ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                                  ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0091 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068AlphaDummy343) ≠ (nb068AlphaDummy347) from (by
                          unfold nb068AlphaDummy347;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0352) 0))))
                      (show (nb068AlphaDummy345 f) ≠ (nb068AlphaDummy348 f) from (by
                          unfold nb068AlphaDummy348;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0353 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy347), (nb068AlphaDummy348 f)),
                      ((nb068AlphaDummy343), (nb068AlphaDummy345 f)),
                      ((nb068AlphaDummy344), (nb068AlphaDummy346 f)),
                      ((nb068AlphaDummy369), (nb068AlphaDummy370 f)),
                      ((nb068AlphaDummy367), (nb068AlphaDummy368 f)),
                      ((nb068AlphaDummy336), (nb068AlphaDummy338 f)),
                      ((nb068AlphaDummy335), (nb068AlphaDummy337 f)),
                      ((nb068AlphaDummy365), (nb068AlphaDummy366 f)),
                      ((nb068AlphaDummy339), (nb068AlphaDummy340 f)),
                      ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                      ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                      ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                      ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                      ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy343) ≠ (nb068AlphaDummy347) from
                      (by
                        unfold nb068AlphaDummy347;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0352) 0))))
                    (show (nb068AlphaDummy345 f) ≠ (nb068AlphaDummy348 f) from (by
                        unfold nb068AlphaDummy348;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0353 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy343) ≠ (nb068AlphaDummy347) from (by
                          unfold nb068AlphaDummy347;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0352) 0))))
                      (show (nb068AlphaDummy345 f) ≠ (nb068AlphaDummy348 f) from (by
                          unfold nb068AlphaDummy348;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0353 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy347), (nb068AlphaDummy348 f)),
                      ((nb068AlphaDummy343), (nb068AlphaDummy345 f)),
                      ((nb068AlphaDummy344), (nb068AlphaDummy346 f)),
                      ((nb068AlphaDummy369), (nb068AlphaDummy370 f)),
                      ((nb068AlphaDummy367), (nb068AlphaDummy368 f)),
                      ((nb068AlphaDummy336), (nb068AlphaDummy338 f)),
                      ((nb068AlphaDummy335), (nb068AlphaDummy337 f)),
                      ((nb068AlphaDummy365), (nb068AlphaDummy366 f)),
                      ((nb068AlphaDummy339), (nb068AlphaDummy340 f)),
                      ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                      ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                      ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                      ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                      ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0093`. -/
@[expose]
noncomputable def nb068SplitAlpha0093 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy365), (nb068AlphaDummy366 f)),
        ((nb068AlphaDummy339), (nb068AlphaDummy340 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy365))
          (Class.cab (nb068AlphaDummy335)
            (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy328))
              (Wff.classEq (Class.cv (nb068AlphaDummy335))
                (synCun (synCphi (Class.cv (nb068AlphaDummy336))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy365))
            (Class.cab (nb068AlphaDummy335)
              (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy328))
                (Wff.classEq (Class.cv (nb068AlphaDummy335))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy336)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy366 f))
          (Class.cab (nb068AlphaDummy337 f)
            (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy331 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy338 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy366 f))
            (Class.cab (nb068AlphaDummy337 f)
              (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy331 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy338 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy336) from
                    (by
                      unfold nb068AlphaDummy336;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0372) 1))))
                  (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy338 f) from (by
                      unfold nb068AlphaDummy338;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0374 f) 1))))
                  (TAlphaVar.there (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy335) from
                      (by
                        unfold nb068AlphaDummy335;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0372) 0))))
                    (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy337 f) from (by
                        unfold nb068AlphaDummy337;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0374 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy365) from (by
                          unfold nb068AlphaDummy365;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0376) 0))))
                      (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy366 f) from (by
                          unfold nb068AlphaDummy366;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0377 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy339) from (by
                            unfold nb068AlphaDummy339;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0373) 0))))
                        (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy340 f) from (by
                            unfold nb068AlphaDummy340;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0375 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy327))).fv ∪
                      ((Class.cv (nb068AlphaDummy328))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068AlphaDummy330 f))).fv ∪
                      ((Class.cv (nb068AlphaDummy331 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0092 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0092 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy367), (nb068AlphaDummy368 f)),
                          ((nb068AlphaDummy336), (nb068AlphaDummy338 f)),
                          ((nb068AlphaDummy335), (nb068AlphaDummy337 f)),
                          ((nb068AlphaDummy365), (nb068AlphaDummy366 f)),
                          ((nb068AlphaDummy339), (nb068AlphaDummy340 f)),
                          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                          ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                          ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy336) from
                      (by
                        unfold nb068AlphaDummy336;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0372) 1))))
                    (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy338 f) from (by
                        unfold nb068AlphaDummy338;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0374 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy335) from (by
                          unfold nb068AlphaDummy335;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0372) 0))))
                      (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy337 f) from (by
                          unfold nb068AlphaDummy337;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0374 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy365) from (by
                            unfold nb068AlphaDummy365;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0376) 0))))
                        (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy366 f) from (by
                            unfold nb068AlphaDummy366;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0377 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy339) from (by
                              unfold nb068AlphaDummy339;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0373) 0))))
                          (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy340 f) from (by
                              unfold nb068AlphaDummy340;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0375 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068AlphaDummy327))).fv ∪
                        ((Class.cv (nb068AlphaDummy328))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy330 f))).fv ∪
                        ((Class.cv (nb068AlphaDummy331 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0092 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0092 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy367), (nb068AlphaDummy368 f)),
                            ((nb068AlphaDummy336), (nb068AlphaDummy338 f)),
                            ((nb068AlphaDummy335), (nb068AlphaDummy337 f)),
                            ((nb068AlphaDummy365), (nb068AlphaDummy366 f)),
                            ((nb068AlphaDummy339), (nb068AlphaDummy340 f)),
                            ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                            ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                            ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                            ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                            ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                            ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                            ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0094`. -/
@[expose]
noncomputable def nb068SplitAlpha0094 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy387), (nb068AlphaDummy390 f)),
        ((nb068AlphaDummy386), (nb068AlphaDummy389 f)),
        ((nb068AlphaDummy385), (nb068AlphaDummy388 f)),
        ((nb068AlphaDummy383), (nb068AlphaDummy384 f)),
        ((nb068AlphaDummy379), (nb068AlphaDummy381 f)),
        ((nb068AlphaDummy380), (nb068AlphaDummy382 f)),
        ((nb068AlphaDummy372), (nb068AlphaDummy374 f)),
        ((nb068AlphaDummy371), (nb068AlphaDummy373 f)),
        ((nb068AlphaDummy377), (nb068AlphaDummy378 f)),
        ((nb068AlphaDummy375), (nb068AlphaDummy376 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy386)) (Class.cv (nb068AlphaDummy387)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy385))
            (synCun (Class.cv (nb068AlphaDummy386)) (Class.cv (nb068AlphaDummy387))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy389 f))
            (Class.cv (nb068AlphaDummy390 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy388 f))
            (synCun (Class.cv (nb068AlphaDummy389 f))
              (Class.cv (nb068AlphaDummy390 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy386) ≠ (nb068AlphaDummy393) from (by
                              unfold nb068AlphaDummy393;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0396) 0))))
                          (show (nb068AlphaDummy389 f) ≠ (nb068AlphaDummy394 f) from (by
                              unfold nb068AlphaDummy394;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0397 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy386) ≠ (nb068AlphaDummy391) from (by
                                unfold nb068AlphaDummy391;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0394) 0))))
                            (show (nb068AlphaDummy389 f) ≠ (nb068AlphaDummy392 f) from (by
                                unfold nb068AlphaDummy392;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0395 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy387) ≠ (nb068AlphaDummy393) from (by
                              unfold nb068AlphaDummy393;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0400) 0))))
                          (show (nb068AlphaDummy390 f) ≠ (nb068AlphaDummy394 f) from (by
                              unfold nb068AlphaDummy394;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0401 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy387) ≠ (nb068AlphaDummy391) from (by
                                unfold nb068AlphaDummy391;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0398) 0))))
                            (show (nb068AlphaDummy390 f) ≠ (nb068AlphaDummy392 f) from (by
                                unfold nb068AlphaDummy392;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0399 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy386) ≠ (nb068AlphaDummy393) from (by
                              unfold nb068AlphaDummy393;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0396) 0))))
                          (show (nb068AlphaDummy389 f) ≠ (nb068AlphaDummy394 f) from (by
                              unfold nb068AlphaDummy394;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0397 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy386) ≠ (nb068AlphaDummy391) from (by
                                unfold nb068AlphaDummy391;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0394) 0))))
                            (show (nb068AlphaDummy389 f) ≠ (nb068AlphaDummy392 f) from (by
                                unfold nb068AlphaDummy392;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0395 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy387) ≠ (nb068AlphaDummy393) from (by
                              unfold nb068AlphaDummy393;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0400) 0))))
                          (show (nb068AlphaDummy390 f) ≠ (nb068AlphaDummy394 f) from (by
                              unfold nb068AlphaDummy394;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0401 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy387) ≠ (nb068AlphaDummy391) from (by
                                unfold nb068AlphaDummy391;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0398) 0))))
                            (show (nb068AlphaDummy390 f) ≠ (nb068AlphaDummy392 f) from (by
                                unfold nb068AlphaDummy392;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0399 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy387), (nb068AlphaDummy390 f)),
          ((nb068AlphaDummy386), (nb068AlphaDummy389 f)),
          ((nb068AlphaDummy385), (nb068AlphaDummy388 f)),
          ((nb068AlphaDummy383), (nb068AlphaDummy384 f)),
          ((nb068AlphaDummy379), (nb068AlphaDummy381 f)),
          ((nb068AlphaDummy380), (nb068AlphaDummy382 f)),
          ((nb068AlphaDummy372), (nb068AlphaDummy374 f)),
          ((nb068AlphaDummy371), (nb068AlphaDummy373 f)),
          ((nb068AlphaDummy377), (nb068AlphaDummy378 f)),
          ((nb068AlphaDummy375), (nb068AlphaDummy376 f)),
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
          ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy386) ≠ (nb068AlphaDummy397) from (by
                                unfold nb068AlphaDummy397;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0404) 0))))
                            (show (nb068AlphaDummy389 f) ≠ (nb068AlphaDummy398 f) from (by
                                unfold nb068AlphaDummy398;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0405 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy386) ≠ (nb068AlphaDummy395) from (by
                                  unfold nb068AlphaDummy395;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0402) 0))))
                              (show (nb068AlphaDummy389 f) ≠ (nb068AlphaDummy396 f) from
                                (by
                                  unfold nb068AlphaDummy396;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0403 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy386) ≠ (nb068AlphaDummy397) from (by
                                unfold nb068AlphaDummy397;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0404) 0))))
                            (show (nb068AlphaDummy389 f) ≠ (nb068AlphaDummy398 f) from (by
                                unfold nb068AlphaDummy398;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0405 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy386) ≠ (nb068AlphaDummy395) from (by
                                  unfold nb068AlphaDummy395;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0402) 0))))
                              (show (nb068AlphaDummy389 f) ≠ (nb068AlphaDummy396 f) from
                                (by
                                  unfold nb068AlphaDummy396;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0403 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy387) ≠ (nb068AlphaDummy399) from (by
                                unfold nb068AlphaDummy399;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0408) 0))))
                            (show (nb068AlphaDummy390 f) ≠ (nb068AlphaDummy400 f) from (by
                                unfold nb068AlphaDummy400;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0409 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy387) ≠ (nb068AlphaDummy395) from (by
                                  unfold nb068AlphaDummy395;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0406) 0))))
                              (show (nb068AlphaDummy390 f) ≠ (nb068AlphaDummy396 f) from
                                (by
                                  unfold nb068AlphaDummy396;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0407 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy387) ≠ (nb068AlphaDummy399) from (by
                                unfold nb068AlphaDummy399;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0408) 0))))
                            (show (nb068AlphaDummy390 f) ≠ (nb068AlphaDummy400 f) from (by
                                unfold nb068AlphaDummy400;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0409 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy387) ≠ (nb068AlphaDummy395) from (by
                                  unfold nb068AlphaDummy395;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0406) 0))))
                              (show (nb068AlphaDummy390 f) ≠ (nb068AlphaDummy396 f) from
                                (by
                                  unfold nb068AlphaDummy396;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0407 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part039`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0095`. -/
@[expose]
noncomputable def nb068SplitAlpha0095 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy379), (nb068AlphaDummy381 f)),
        ((nb068AlphaDummy380), (nb068AlphaDummy382 f)),
        ((nb068AlphaDummy372), (nb068AlphaDummy374 f)),
        ((nb068AlphaDummy371), (nb068AlphaDummy373 f)),
        ((nb068AlphaDummy377), (nb068AlphaDummy378 f)),
        ((nb068AlphaDummy375), (nb068AlphaDummy376 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy379))
          (Class.cv (nb068AlphaDummy372))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy380))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy379)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy379)) (synC1c))
              (Class.cv (nb068AlphaDummy379))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy381 f))
          (Class.cv (nb068AlphaDummy374 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy382 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy381 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy381 f)) (synC1c))
              (Class.cv (nb068AlphaDummy381 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy372) ≠ (nb068AlphaDummy379) from (by
              unfold nb068AlphaDummy379;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0388) 0))))
          (show (nb068AlphaDummy374 f) ≠ (nb068AlphaDummy381 f) from (by
              unfold nb068AlphaDummy381;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0389 f) 0))))
          (TAlphaVar.there (show (nb068AlphaDummy372) ≠ (nb068AlphaDummy380) from (by
                unfold nb068AlphaDummy380;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0388) 1))))
            (show (nb068AlphaDummy374 f) ≠ (nb068AlphaDummy382 f) from (by
                unfold nb068AlphaDummy382;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0389 f) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy372))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068AlphaDummy374 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy379) ≠ (nb068AlphaDummy386) from (by
                                  unfold nb068AlphaDummy386;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0392) 1))))
                              (show (nb068AlphaDummy381 f) ≠ (nb068AlphaDummy389 f) from
                                (by
                                  unfold nb068AlphaDummy389;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0393 f) 1))))
                              (TAlphaVar.there
                                (show (nb068AlphaDummy379) ≠ (nb068AlphaDummy385) from (by
                                    unfold nb068AlphaDummy385;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0392) 0)))) (show
                                  (nb068AlphaDummy381 f) ≠ (nb068AlphaDummy388 f) from (by
                                    unfold nb068AlphaDummy388;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0393 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy379) ≠ (nb068AlphaDummy383) from
                                    (by
                                      unfold nb068AlphaDummy383;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0390)
                                              0)))) (show
                                    (nb068AlphaDummy381 f) ≠ (nb068AlphaDummy384 f) from
                                    (by
                                      unfold nb068AlphaDummy384;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0391 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy387), (nb068AlphaDummy390 f)),
                                  ((nb068AlphaDummy386), (nb068AlphaDummy389 f)),
                                  ((nb068AlphaDummy385), (nb068AlphaDummy388 f)),
                                  ((nb068AlphaDummy383), (nb068AlphaDummy384 f)),
                                  ((nb068AlphaDummy379), (nb068AlphaDummy381 f)),
                                  ((nb068AlphaDummy380), (nb068AlphaDummy382 f)),
                                  ((nb068AlphaDummy372), (nb068AlphaDummy374 f)),
                                  ((nb068AlphaDummy371), (nb068AlphaDummy373 f)),
                                  ((nb068AlphaDummy377), (nb068AlphaDummy378 f)),
                                  ((nb068AlphaDummy375), (nb068AlphaDummy376 f)),
                                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                                  ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                                  ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0094 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068AlphaDummy379) ≠ (nb068AlphaDummy383) from (by
                          unfold nb068AlphaDummy383;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0390) 0))))
                      (show (nb068AlphaDummy381 f) ≠ (nb068AlphaDummy384 f) from (by
                          unfold nb068AlphaDummy384;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0391 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy383), (nb068AlphaDummy384 f)),
                      ((nb068AlphaDummy379), (nb068AlphaDummy381 f)),
                      ((nb068AlphaDummy380), (nb068AlphaDummy382 f)),
                      ((nb068AlphaDummy372), (nb068AlphaDummy374 f)),
                      ((nb068AlphaDummy371), (nb068AlphaDummy373 f)),
                      ((nb068AlphaDummy377), (nb068AlphaDummy378 f)),
                      ((nb068AlphaDummy375), (nb068AlphaDummy376 f)),
                      ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                      ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                      ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                      ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                      ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                      ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy379) ≠ (nb068AlphaDummy383) from
                      (by
                        unfold nb068AlphaDummy383;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0390) 0))))
                    (show (nb068AlphaDummy381 f) ≠ (nb068AlphaDummy384 f) from (by
                        unfold nb068AlphaDummy384;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0391 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy379) ≠ (nb068AlphaDummy383) from (by
                          unfold nb068AlphaDummy383;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0390) 0))))
                      (show (nb068AlphaDummy381 f) ≠ (nb068AlphaDummy384 f) from (by
                          unfold nb068AlphaDummy384;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0391 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy383), (nb068AlphaDummy384 f)),
                      ((nb068AlphaDummy379), (nb068AlphaDummy381 f)),
                      ((nb068AlphaDummy380), (nb068AlphaDummy382 f)),
                      ((nb068AlphaDummy372), (nb068AlphaDummy374 f)),
                      ((nb068AlphaDummy371), (nb068AlphaDummy373 f)),
                      ((nb068AlphaDummy377), (nb068AlphaDummy378 f)),
                      ((nb068AlphaDummy375), (nb068AlphaDummy376 f)),
                      ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                      ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                      ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                      ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                      ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                      ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0096`. -/
@[expose]
noncomputable def nb068SplitAlpha0096 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy387), (nb068AlphaDummy390 f)),
        ((nb068AlphaDummy386), (nb068AlphaDummy389 f)),
        ((nb068AlphaDummy385), (nb068AlphaDummy388 f)),
        ((nb068AlphaDummy383), (nb068AlphaDummy384 f)),
        ((nb068AlphaDummy379), (nb068AlphaDummy381 f)),
        ((nb068AlphaDummy380), (nb068AlphaDummy382 f)),
        ((nb068AlphaDummy405), (nb068AlphaDummy406 f)),
        ((nb068AlphaDummy403), (nb068AlphaDummy404 f)),
        ((nb068AlphaDummy372), (nb068AlphaDummy374 f)),
        ((nb068AlphaDummy371), (nb068AlphaDummy373 f)),
        ((nb068AlphaDummy401), (nb068AlphaDummy402 f)),
        ((nb068AlphaDummy375), (nb068AlphaDummy376 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy386)) (Class.cv (nb068AlphaDummy387)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy385))
            (synCun (Class.cv (nb068AlphaDummy386)) (Class.cv (nb068AlphaDummy387))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy389 f))
            (Class.cv (nb068AlphaDummy390 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy388 f))
            (synCun (Class.cv (nb068AlphaDummy389 f))
              (Class.cv (nb068AlphaDummy390 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy386) ≠ (nb068AlphaDummy393) from (by
                              unfold nb068AlphaDummy393;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0396) 0))))
                          (show (nb068AlphaDummy389 f) ≠ (nb068AlphaDummy394 f) from (by
                              unfold nb068AlphaDummy394;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0397 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy386) ≠ (nb068AlphaDummy391) from (by
                                unfold nb068AlphaDummy391;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0394) 0))))
                            (show (nb068AlphaDummy389 f) ≠ (nb068AlphaDummy392 f) from (by
                                unfold nb068AlphaDummy392;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0395 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy387) ≠ (nb068AlphaDummy393) from (by
                              unfold nb068AlphaDummy393;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0400) 0))))
                          (show (nb068AlphaDummy390 f) ≠ (nb068AlphaDummy394 f) from (by
                              unfold nb068AlphaDummy394;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0401 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy387) ≠ (nb068AlphaDummy391) from (by
                                unfold nb068AlphaDummy391;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0398) 0))))
                            (show (nb068AlphaDummy390 f) ≠ (nb068AlphaDummy392 f) from (by
                                unfold nb068AlphaDummy392;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0399 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy386) ≠ (nb068AlphaDummy393) from (by
                              unfold nb068AlphaDummy393;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0396) 0))))
                          (show (nb068AlphaDummy389 f) ≠ (nb068AlphaDummy394 f) from (by
                              unfold nb068AlphaDummy394;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0397 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy386) ≠ (nb068AlphaDummy391) from (by
                                unfold nb068AlphaDummy391;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0394) 0))))
                            (show (nb068AlphaDummy389 f) ≠ (nb068AlphaDummy392 f) from (by
                                unfold nb068AlphaDummy392;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0395 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy387) ≠ (nb068AlphaDummy393) from (by
                              unfold nb068AlphaDummy393;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0400) 0))))
                          (show (nb068AlphaDummy390 f) ≠ (nb068AlphaDummy394 f) from (by
                              unfold nb068AlphaDummy394;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0401 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy387) ≠ (nb068AlphaDummy391) from (by
                                unfold nb068AlphaDummy391;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0398) 0))))
                            (show (nb068AlphaDummy390 f) ≠ (nb068AlphaDummy392 f) from (by
                                unfold nb068AlphaDummy392;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0399 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy387), (nb068AlphaDummy390 f)),
          ((nb068AlphaDummy386), (nb068AlphaDummy389 f)),
          ((nb068AlphaDummy385), (nb068AlphaDummy388 f)),
          ((nb068AlphaDummy383), (nb068AlphaDummy384 f)),
          ((nb068AlphaDummy379), (nb068AlphaDummy381 f)),
          ((nb068AlphaDummy380), (nb068AlphaDummy382 f)),
          ((nb068AlphaDummy405), (nb068AlphaDummy406 f)),
          ((nb068AlphaDummy403), (nb068AlphaDummy404 f)),
          ((nb068AlphaDummy372), (nb068AlphaDummy374 f)),
          ((nb068AlphaDummy371), (nb068AlphaDummy373 f)),
          ((nb068AlphaDummy401), (nb068AlphaDummy402 f)),
          ((nb068AlphaDummy375), (nb068AlphaDummy376 f)),
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
          ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy386) ≠ (nb068AlphaDummy397) from (by
                                unfold nb068AlphaDummy397;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0404) 0))))
                            (show (nb068AlphaDummy389 f) ≠ (nb068AlphaDummy398 f) from (by
                                unfold nb068AlphaDummy398;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0405 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy386) ≠ (nb068AlphaDummy395) from (by
                                  unfold nb068AlphaDummy395;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0402) 0))))
                              (show (nb068AlphaDummy389 f) ≠ (nb068AlphaDummy396 f) from
                                (by
                                  unfold nb068AlphaDummy396;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0403 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy386) ≠ (nb068AlphaDummy397) from (by
                                unfold nb068AlphaDummy397;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0404) 0))))
                            (show (nb068AlphaDummy389 f) ≠ (nb068AlphaDummy398 f) from (by
                                unfold nb068AlphaDummy398;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0405 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy386) ≠ (nb068AlphaDummy395) from (by
                                  unfold nb068AlphaDummy395;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0402) 0))))
                              (show (nb068AlphaDummy389 f) ≠ (nb068AlphaDummy396 f) from
                                (by
                                  unfold nb068AlphaDummy396;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0403 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy387) ≠ (nb068AlphaDummy399) from (by
                                unfold nb068AlphaDummy399;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0408) 0))))
                            (show (nb068AlphaDummy390 f) ≠ (nb068AlphaDummy400 f) from (by
                                unfold nb068AlphaDummy400;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0409 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy387) ≠ (nb068AlphaDummy395) from (by
                                  unfold nb068AlphaDummy395;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0406) 0))))
                              (show (nb068AlphaDummy390 f) ≠ (nb068AlphaDummy396 f) from
                                (by
                                  unfold nb068AlphaDummy396;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0407 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy387) ≠ (nb068AlphaDummy399) from (by
                                unfold nb068AlphaDummy399;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0408) 0))))
                            (show (nb068AlphaDummy390 f) ≠ (nb068AlphaDummy400 f) from (by
                                unfold nb068AlphaDummy400;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0409 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy387) ≠ (nb068AlphaDummy395) from (by
                                  unfold nb068AlphaDummy395;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0406) 0))))
                              (show (nb068AlphaDummy390 f) ≠ (nb068AlphaDummy396 f) from
                                (by
                                  unfold nb068AlphaDummy396;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0407 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0097`. -/
@[expose]
noncomputable def nb068SplitAlpha0097 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy379), (nb068AlphaDummy381 f)),
        ((nb068AlphaDummy380), (nb068AlphaDummy382 f)),
        ((nb068AlphaDummy405), (nb068AlphaDummy406 f)),
        ((nb068AlphaDummy403), (nb068AlphaDummy404 f)),
        ((nb068AlphaDummy372), (nb068AlphaDummy374 f)),
        ((nb068AlphaDummy371), (nb068AlphaDummy373 f)),
        ((nb068AlphaDummy401), (nb068AlphaDummy402 f)),
        ((nb068AlphaDummy375), (nb068AlphaDummy376 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy379))
          (Class.cv (nb068AlphaDummy372))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy380))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy379)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy379)) (synC1c))
              (Class.cv (nb068AlphaDummy379))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy381 f))
          (Class.cv (nb068AlphaDummy374 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy382 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy381 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy381 f)) (synC1c))
              (Class.cv (nb068AlphaDummy381 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy372) ≠ (nb068AlphaDummy379) from (by
              unfold nb068AlphaDummy379;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0388) 0))))
          (show (nb068AlphaDummy374 f) ≠ (nb068AlphaDummy381 f) from (by
              unfold nb068AlphaDummy381;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0389 f) 0))))
          (TAlphaVar.there (show (nb068AlphaDummy372) ≠ (nb068AlphaDummy380) from (by
                unfold nb068AlphaDummy380;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0388) 1))))
            (show (nb068AlphaDummy374 f) ≠ (nb068AlphaDummy382 f) from (by
                unfold nb068AlphaDummy382;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0389 f) 1))))
            (TAlphaVar.there (show (nb068AlphaDummy372) ≠ (nb068AlphaDummy405) from (by
                  unfold nb068AlphaDummy405;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0418) 0))))
              (show (nb068AlphaDummy374 f) ≠ (nb068AlphaDummy406 f) from (by
                  unfold nb068AlphaDummy406;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0419 f) 0))))
              (TAlphaVar.there (show (nb068AlphaDummy372) ≠ (nb068AlphaDummy403) from (by
                    unfold nb068AlphaDummy403;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0416) 0))))
                (show (nb068AlphaDummy374 f) ≠ (nb068AlphaDummy404 f) from (by
                    unfold nb068AlphaDummy404;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0417 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy372))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068AlphaDummy374 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy379) ≠ (nb068AlphaDummy386) from (by
                                  unfold nb068AlphaDummy386;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0392) 1))))
                              (show (nb068AlphaDummy381 f) ≠ (nb068AlphaDummy389 f) from
                                (by
                                  unfold nb068AlphaDummy389;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0393 f) 1))))
                              (TAlphaVar.there
                                (show (nb068AlphaDummy379) ≠ (nb068AlphaDummy385) from (by
                                    unfold nb068AlphaDummy385;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0392) 0)))) (show
                                  (nb068AlphaDummy381 f) ≠ (nb068AlphaDummy388 f) from (by
                                    unfold nb068AlphaDummy388;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0393 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy379) ≠ (nb068AlphaDummy383) from
                                    (by
                                      unfold nb068AlphaDummy383;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0390)
                                              0)))) (show
                                    (nb068AlphaDummy381 f) ≠ (nb068AlphaDummy384 f) from
                                    (by
                                      unfold nb068AlphaDummy384;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0391 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy387), (nb068AlphaDummy390 f)),
                                  ((nb068AlphaDummy386), (nb068AlphaDummy389 f)),
                                  ((nb068AlphaDummy385), (nb068AlphaDummy388 f)),
                                  ((nb068AlphaDummy383), (nb068AlphaDummy384 f)),
                                  ((nb068AlphaDummy379), (nb068AlphaDummy381 f)),
                                  ((nb068AlphaDummy380), (nb068AlphaDummy382 f)),
                                  ((nb068AlphaDummy405), (nb068AlphaDummy406 f)),
                                  ((nb068AlphaDummy403), (nb068AlphaDummy404 f)),
                                  ((nb068AlphaDummy372), (nb068AlphaDummy374 f)),
                                  ((nb068AlphaDummy371), (nb068AlphaDummy373 f)),
                                  ((nb068AlphaDummy401), (nb068AlphaDummy402 f)),
                                  ((nb068AlphaDummy375), (nb068AlphaDummy376 f)),
                                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                                  ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                                  ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0096 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068AlphaDummy379) ≠ (nb068AlphaDummy383) from (by
                          unfold nb068AlphaDummy383;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0390) 0))))
                      (show (nb068AlphaDummy381 f) ≠ (nb068AlphaDummy384 f) from (by
                          unfold nb068AlphaDummy384;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0391 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy383), (nb068AlphaDummy384 f)),
                      ((nb068AlphaDummy379), (nb068AlphaDummy381 f)),
                      ((nb068AlphaDummy380), (nb068AlphaDummy382 f)),
                      ((nb068AlphaDummy405), (nb068AlphaDummy406 f)),
                      ((nb068AlphaDummy403), (nb068AlphaDummy404 f)),
                      ((nb068AlphaDummy372), (nb068AlphaDummy374 f)),
                      ((nb068AlphaDummy371), (nb068AlphaDummy373 f)),
                      ((nb068AlphaDummy401), (nb068AlphaDummy402 f)),
                      ((nb068AlphaDummy375), (nb068AlphaDummy376 f)),
                      ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                      ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                      ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                      ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                      ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                      ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy379) ≠ (nb068AlphaDummy383) from
                      (by
                        unfold nb068AlphaDummy383;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0390) 0))))
                    (show (nb068AlphaDummy381 f) ≠ (nb068AlphaDummy384 f) from (by
                        unfold nb068AlphaDummy384;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0391 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy379) ≠ (nb068AlphaDummy383) from (by
                          unfold nb068AlphaDummy383;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0390) 0))))
                      (show (nb068AlphaDummy381 f) ≠ (nb068AlphaDummy384 f) from (by
                          unfold nb068AlphaDummy384;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0391 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy383), (nb068AlphaDummy384 f)),
                      ((nb068AlphaDummy379), (nb068AlphaDummy381 f)),
                      ((nb068AlphaDummy380), (nb068AlphaDummy382 f)),
                      ((nb068AlphaDummy405), (nb068AlphaDummy406 f)),
                      ((nb068AlphaDummy403), (nb068AlphaDummy404 f)),
                      ((nb068AlphaDummy372), (nb068AlphaDummy374 f)),
                      ((nb068AlphaDummy371), (nb068AlphaDummy373 f)),
                      ((nb068AlphaDummy401), (nb068AlphaDummy402 f)),
                      ((nb068AlphaDummy375), (nb068AlphaDummy376 f)),
                      ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                      ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                      ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                      ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                      ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                      ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0098`. -/
@[expose]
noncomputable def nb068SplitAlpha0098 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy401), (nb068AlphaDummy402 f)),
        ((nb068AlphaDummy375), (nb068AlphaDummy376 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy401))
          (Class.cab (nb068AlphaDummy371)
            (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy329))
              (Wff.classEq (Class.cv (nb068AlphaDummy371))
                (synCun (synCphi (Class.cv (nb068AlphaDummy372))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy401))
            (Class.cab (nb068AlphaDummy371)
              (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy329))
                (Wff.classEq (Class.cv (nb068AlphaDummy371))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy372)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy402 f))
          (Class.cab (nb068AlphaDummy373 f)
            (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy332 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy374 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy402 f))
            (Class.cab (nb068AlphaDummy373 f)
              (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy332 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy374 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy329) ≠ (nb068AlphaDummy372) from
                    (by
                      unfold nb068AlphaDummy372;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0410) 1))))
                  (show (nb068AlphaDummy332 f) ≠ (nb068AlphaDummy374 f) from (by
                      unfold nb068AlphaDummy374;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0412 f) 1))))
                  (TAlphaVar.there (show (nb068AlphaDummy329) ≠ (nb068AlphaDummy371) from
                      (by
                        unfold nb068AlphaDummy371;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0410) 0))))
                    (show (nb068AlphaDummy332 f) ≠ (nb068AlphaDummy373 f) from (by
                        unfold nb068AlphaDummy373;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0412 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy329) ≠ (nb068AlphaDummy401) from (by
                          unfold nb068AlphaDummy401;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0414) 0))))
                      (show (nb068AlphaDummy332 f) ≠ (nb068AlphaDummy402 f) from (by
                          unfold nb068AlphaDummy402;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0415 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy329) ≠ (nb068AlphaDummy375) from (by
                            unfold nb068AlphaDummy375;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0411) 0))))
                        (show (nb068AlphaDummy332 f) ≠ (nb068AlphaDummy376 f) from (by
                            unfold nb068AlphaDummy376;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0413 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy327))).fv ∪
                      ((Class.cv (nb068AlphaDummy329))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068AlphaDummy330 f))).fv ∪
                      ((Class.cv (nb068AlphaDummy332 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0097 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0097 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy403), (nb068AlphaDummy404 f)),
                          ((nb068AlphaDummy372), (nb068AlphaDummy374 f)),
                          ((nb068AlphaDummy371), (nb068AlphaDummy373 f)),
                          ((nb068AlphaDummy401), (nb068AlphaDummy402 f)),
                          ((nb068AlphaDummy375), (nb068AlphaDummy376 f)),
                          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                          ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                          ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy329) ≠ (nb068AlphaDummy372) from
                      (by
                        unfold nb068AlphaDummy372;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0410) 1))))
                    (show (nb068AlphaDummy332 f) ≠ (nb068AlphaDummy374 f) from (by
                        unfold nb068AlphaDummy374;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0412 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy329) ≠ (nb068AlphaDummy371) from (by
                          unfold nb068AlphaDummy371;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0410) 0))))
                      (show (nb068AlphaDummy332 f) ≠ (nb068AlphaDummy373 f) from (by
                          unfold nb068AlphaDummy373;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0412 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy329) ≠ (nb068AlphaDummy401) from (by
                            unfold nb068AlphaDummy401;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0414) 0))))
                        (show (nb068AlphaDummy332 f) ≠ (nb068AlphaDummy402 f) from (by
                            unfold nb068AlphaDummy402;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0415 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy329) ≠ (nb068AlphaDummy375) from (by
                              unfold nb068AlphaDummy375;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0411) 0))))
                          (show (nb068AlphaDummy332 f) ≠ (nb068AlphaDummy376 f) from (by
                              unfold nb068AlphaDummy376;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0413 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068AlphaDummy327))).fv ∪
                        ((Class.cv (nb068AlphaDummy329))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy330 f))).fv ∪
                        ((Class.cv (nb068AlphaDummy332 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0097 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0097 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy403), (nb068AlphaDummy404 f)),
                            ((nb068AlphaDummy372), (nb068AlphaDummy374 f)),
                            ((nb068AlphaDummy371), (nb068AlphaDummy373 f)),
                            ((nb068AlphaDummy401), (nb068AlphaDummy402 f)),
                            ((nb068AlphaDummy375), (nb068AlphaDummy376 f)),
                            ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                            ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                            ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                            ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                            ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                            ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                            ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                            ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part040`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0099`. -/
@[expose]
noncomputable def nb068SplitAlpha0099 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy429), (nb068AlphaDummy432 f)),
        ((nb068AlphaDummy428), (nb068AlphaDummy431 f)),
        ((nb068AlphaDummy427), (nb068AlphaDummy430 f)),
        ((nb068AlphaDummy425), (nb068AlphaDummy426 f)),
        ((nb068AlphaDummy421), (nb068AlphaDummy423 f)),
        ((nb068AlphaDummy422), (nb068AlphaDummy424 f)),
        ((nb068AlphaDummy414), (nb068AlphaDummy416 f)),
        ((nb068AlphaDummy413), (nb068AlphaDummy415 f)),
        ((nb068AlphaDummy419), (nb068AlphaDummy420 f)),
        ((nb068AlphaDummy417), (nb068AlphaDummy418 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy428)) (Class.cv (nb068AlphaDummy429)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy427))
            (synCun (Class.cv (nb068AlphaDummy428)) (Class.cv (nb068AlphaDummy429))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy431 f))
            (Class.cv (nb068AlphaDummy432 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy430 f))
            (synCun (Class.cv (nb068AlphaDummy431 f))
              (Class.cv (nb068AlphaDummy432 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy428) ≠ (nb068AlphaDummy435) from (by
                              unfold nb068AlphaDummy435;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0438) 0))))
                          (show (nb068AlphaDummy431 f) ≠ (nb068AlphaDummy436 f) from (by
                              unfold nb068AlphaDummy436;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0439 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy428) ≠ (nb068AlphaDummy433) from (by
                                unfold nb068AlphaDummy433;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0436) 0))))
                            (show (nb068AlphaDummy431 f) ≠ (nb068AlphaDummy434 f) from (by
                                unfold nb068AlphaDummy434;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0437 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy429) ≠ (nb068AlphaDummy435) from (by
                              unfold nb068AlphaDummy435;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0442) 0))))
                          (show (nb068AlphaDummy432 f) ≠ (nb068AlphaDummy436 f) from (by
                              unfold nb068AlphaDummy436;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0443 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy429) ≠ (nb068AlphaDummy433) from (by
                                unfold nb068AlphaDummy433;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0440) 0))))
                            (show (nb068AlphaDummy432 f) ≠ (nb068AlphaDummy434 f) from (by
                                unfold nb068AlphaDummy434;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0441 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy428) ≠ (nb068AlphaDummy435) from (by
                              unfold nb068AlphaDummy435;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0438) 0))))
                          (show (nb068AlphaDummy431 f) ≠ (nb068AlphaDummy436 f) from (by
                              unfold nb068AlphaDummy436;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0439 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy428) ≠ (nb068AlphaDummy433) from (by
                                unfold nb068AlphaDummy433;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0436) 0))))
                            (show (nb068AlphaDummy431 f) ≠ (nb068AlphaDummy434 f) from (by
                                unfold nb068AlphaDummy434;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0437 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy429) ≠ (nb068AlphaDummy435) from (by
                              unfold nb068AlphaDummy435;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0442) 0))))
                          (show (nb068AlphaDummy432 f) ≠ (nb068AlphaDummy436 f) from (by
                              unfold nb068AlphaDummy436;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0443 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy429) ≠ (nb068AlphaDummy433) from (by
                                unfold nb068AlphaDummy433;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0440) 0))))
                            (show (nb068AlphaDummy432 f) ≠ (nb068AlphaDummy434 f) from (by
                                unfold nb068AlphaDummy434;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0441 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy429), (nb068AlphaDummy432 f)),
          ((nb068AlphaDummy428), (nb068AlphaDummy431 f)),
          ((nb068AlphaDummy427), (nb068AlphaDummy430 f)),
          ((nb068AlphaDummy425), (nb068AlphaDummy426 f)),
          ((nb068AlphaDummy421), (nb068AlphaDummy423 f)),
          ((nb068AlphaDummy422), (nb068AlphaDummy424 f)),
          ((nb068AlphaDummy414), (nb068AlphaDummy416 f)),
          ((nb068AlphaDummy413), (nb068AlphaDummy415 f)),
          ((nb068AlphaDummy419), (nb068AlphaDummy420 f)),
          ((nb068AlphaDummy417), (nb068AlphaDummy418 f)),
          ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
          ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
          ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
          ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy428) ≠ (nb068AlphaDummy439) from (by
                                unfold nb068AlphaDummy439;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0446) 0))))
                            (show (nb068AlphaDummy431 f) ≠ (nb068AlphaDummy440 f) from (by
                                unfold nb068AlphaDummy440;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0447 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy428) ≠ (nb068AlphaDummy437) from (by
                                  unfold nb068AlphaDummy437;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0444) 0))))
                              (show (nb068AlphaDummy431 f) ≠ (nb068AlphaDummy438 f) from
                                (by
                                  unfold nb068AlphaDummy438;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0445 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy428) ≠ (nb068AlphaDummy439) from (by
                                unfold nb068AlphaDummy439;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0446) 0))))
                            (show (nb068AlphaDummy431 f) ≠ (nb068AlphaDummy440 f) from (by
                                unfold nb068AlphaDummy440;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0447 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy428) ≠ (nb068AlphaDummy437) from (by
                                  unfold nb068AlphaDummy437;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0444) 0))))
                              (show (nb068AlphaDummy431 f) ≠ (nb068AlphaDummy438 f) from
                                (by
                                  unfold nb068AlphaDummy438;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0445 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy429) ≠ (nb068AlphaDummy441) from (by
                                unfold nb068AlphaDummy441;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0450) 0))))
                            (show (nb068AlphaDummy432 f) ≠ (nb068AlphaDummy442 f) from (by
                                unfold nb068AlphaDummy442;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0451 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy429) ≠ (nb068AlphaDummy437) from (by
                                  unfold nb068AlphaDummy437;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0448) 0))))
                              (show (nb068AlphaDummy432 f) ≠ (nb068AlphaDummy438 f) from
                                (by
                                  unfold nb068AlphaDummy438;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0449 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy429) ≠ (nb068AlphaDummy441) from (by
                                unfold nb068AlphaDummy441;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0450) 0))))
                            (show (nb068AlphaDummy432 f) ≠ (nb068AlphaDummy442 f) from (by
                                unfold nb068AlphaDummy442;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0451 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy429) ≠ (nb068AlphaDummy437) from (by
                                  unfold nb068AlphaDummy437;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0448) 0))))
                              (show (nb068AlphaDummy432 f) ≠ (nb068AlphaDummy438 f) from
                                (by
                                  unfold nb068AlphaDummy438;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0449 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0100`. -/
@[expose]
noncomputable def nb068SplitAlpha0100 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy421), (nb068AlphaDummy423 f)),
        ((nb068AlphaDummy422), (nb068AlphaDummy424 f)),
        ((nb068AlphaDummy414), (nb068AlphaDummy416 f)),
        ((nb068AlphaDummy413), (nb068AlphaDummy415 f)),
        ((nb068AlphaDummy419), (nb068AlphaDummy420 f)),
        ((nb068AlphaDummy417), (nb068AlphaDummy418 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classEq (Class.cv (nb068AlphaDummy422))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy421)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy421)) (synC1c))
          (Class.cv (nb068AlphaDummy421))))
      (Wff.classEq (Class.cv (nb068AlphaDummy424 f))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy423 f)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy423 f)) (synC1c))
          (Class.cv (nb068AlphaDummy423 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068AlphaDummy414))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb068AlphaDummy416 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy421) ≠ (nb068AlphaDummy428) from (by
                              unfold nb068AlphaDummy428;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0434) 1))))
                          (show (nb068AlphaDummy423 f) ≠ (nb068AlphaDummy431 f) from (by
                              unfold nb068AlphaDummy431;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0435 f) 1))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy421) ≠ (nb068AlphaDummy427) from (by
                                unfold nb068AlphaDummy427;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0434) 0))))
                            (show (nb068AlphaDummy423 f) ≠ (nb068AlphaDummy430 f) from (by
                                unfold nb068AlphaDummy430;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0435 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy421) ≠ (nb068AlphaDummy425) from (by
                                  unfold nb068AlphaDummy425;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0432) 0))))
                              (show (nb068AlphaDummy423 f) ≠ (nb068AlphaDummy426 f) from
                                (by
                                  unfold nb068AlphaDummy426;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0433 f) 0))))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb068AlphaDummy429), (nb068AlphaDummy432 f)),
                              ((nb068AlphaDummy428), (nb068AlphaDummy431 f)),
                              ((nb068AlphaDummy427), (nb068AlphaDummy430 f)),
                              ((nb068AlphaDummy425), (nb068AlphaDummy426 f)),
                              ((nb068AlphaDummy421), (nb068AlphaDummy423 f)),
                              ((nb068AlphaDummy422), (nb068AlphaDummy424 f)),
                              ((nb068AlphaDummy414), (nb068AlphaDummy416 f)),
                              ((nb068AlphaDummy413), (nb068AlphaDummy415 f)),
                              ((nb068AlphaDummy419), (nb068AlphaDummy420 f)),
                              ((nb068AlphaDummy417), (nb068AlphaDummy418 f)),
                              ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                              ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                              ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                              ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                              ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                              ((nb068AlphaDummy001), x),
                              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                            (synC1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb068SplitAlpha0099 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb068AlphaDummy421) ≠ (nb068AlphaDummy425) from (by
                      unfold nb068AlphaDummy425;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0432) 0))))
                  (show (nb068AlphaDummy423 f) ≠ (nb068AlphaDummy426 f) from (by
                      unfold nb068AlphaDummy426;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0433 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb068AlphaDummy425), (nb068AlphaDummy426 f)),
                  ((nb068AlphaDummy421), (nb068AlphaDummy423 f)),
                  ((nb068AlphaDummy422), (nb068AlphaDummy424 f)),
                  ((nb068AlphaDummy414), (nb068AlphaDummy416 f)),
                  ((nb068AlphaDummy413), (nb068AlphaDummy415 f)),
                  ((nb068AlphaDummy419), (nb068AlphaDummy420 f)),
                  ((nb068AlphaDummy417), (nb068AlphaDummy418 f)),
                  ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                  ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                  ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                  ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                  ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                  ((nb068AlphaDummy001), x),
                  ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068AlphaDummy421) ≠ (nb068AlphaDummy425) from (by
                    unfold nb068AlphaDummy425;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0432) 0))))
                (show (nb068AlphaDummy423 f) ≠ (nb068AlphaDummy426 f) from (by
                    unfold nb068AlphaDummy426;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0433 f) 0))))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy421) ≠ (nb068AlphaDummy425) from
                    (by
                      unfold nb068AlphaDummy425;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0432) 0))))
                  (show (nb068AlphaDummy423 f) ≠ (nb068AlphaDummy426 f) from (by
                      unfold nb068AlphaDummy426;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0433 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb068AlphaDummy425), (nb068AlphaDummy426 f)),
                  ((nb068AlphaDummy421), (nb068AlphaDummy423 f)),
                  ((nb068AlphaDummy422), (nb068AlphaDummy424 f)),
                  ((nb068AlphaDummy414), (nb068AlphaDummy416 f)),
                  ((nb068AlphaDummy413), (nb068AlphaDummy415 f)),
                  ((nb068AlphaDummy419), (nb068AlphaDummy420 f)),
                  ((nb068AlphaDummy417), (nb068AlphaDummy418 f)),
                  ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                  ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                  ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                  ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                  ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                  ((nb068AlphaDummy001), x),
                  ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part041`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0101`. -/
@[expose]
noncomputable def nb068SplitAlpha0101 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy429), (nb068AlphaDummy432 f)),
        ((nb068AlphaDummy428), (nb068AlphaDummy431 f)),
        ((nb068AlphaDummy427), (nb068AlphaDummy430 f)),
        ((nb068AlphaDummy425), (nb068AlphaDummy426 f)),
        ((nb068AlphaDummy421), (nb068AlphaDummy423 f)),
        ((nb068AlphaDummy422), (nb068AlphaDummy424 f)),
        ((nb068AlphaDummy447), (nb068AlphaDummy448 f)),
        ((nb068AlphaDummy445), (nb068AlphaDummy446 f)),
        ((nb068AlphaDummy414), (nb068AlphaDummy416 f)),
        ((nb068AlphaDummy413), (nb068AlphaDummy415 f)),
        ((nb068AlphaDummy443), (nb068AlphaDummy444 f)),
        ((nb068AlphaDummy417), (nb068AlphaDummy418 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy428)) (Class.cv (nb068AlphaDummy429)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy427))
            (synCun (Class.cv (nb068AlphaDummy428)) (Class.cv (nb068AlphaDummy429))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy431 f))
            (Class.cv (nb068AlphaDummy432 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy430 f))
            (synCun (Class.cv (nb068AlphaDummy431 f))
              (Class.cv (nb068AlphaDummy432 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy428) ≠ (nb068AlphaDummy435) from (by
                              unfold nb068AlphaDummy435;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0438) 0))))
                          (show (nb068AlphaDummy431 f) ≠ (nb068AlphaDummy436 f) from (by
                              unfold nb068AlphaDummy436;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0439 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy428) ≠ (nb068AlphaDummy433) from (by
                                unfold nb068AlphaDummy433;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0436) 0))))
                            (show (nb068AlphaDummy431 f) ≠ (nb068AlphaDummy434 f) from (by
                                unfold nb068AlphaDummy434;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0437 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy429) ≠ (nb068AlphaDummy435) from (by
                              unfold nb068AlphaDummy435;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0442) 0))))
                          (show (nb068AlphaDummy432 f) ≠ (nb068AlphaDummy436 f) from (by
                              unfold nb068AlphaDummy436;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0443 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy429) ≠ (nb068AlphaDummy433) from (by
                                unfold nb068AlphaDummy433;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0440) 0))))
                            (show (nb068AlphaDummy432 f) ≠ (nb068AlphaDummy434 f) from (by
                                unfold nb068AlphaDummy434;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0441 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy428) ≠ (nb068AlphaDummy435) from (by
                              unfold nb068AlphaDummy435;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0438) 0))))
                          (show (nb068AlphaDummy431 f) ≠ (nb068AlphaDummy436 f) from (by
                              unfold nb068AlphaDummy436;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0439 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy428) ≠ (nb068AlphaDummy433) from (by
                                unfold nb068AlphaDummy433;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0436) 0))))
                            (show (nb068AlphaDummy431 f) ≠ (nb068AlphaDummy434 f) from (by
                                unfold nb068AlphaDummy434;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0437 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy429) ≠ (nb068AlphaDummy435) from (by
                              unfold nb068AlphaDummy435;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0442) 0))))
                          (show (nb068AlphaDummy432 f) ≠ (nb068AlphaDummy436 f) from (by
                              unfold nb068AlphaDummy436;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0443 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy429) ≠ (nb068AlphaDummy433) from (by
                                unfold nb068AlphaDummy433;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0440) 0))))
                            (show (nb068AlphaDummy432 f) ≠ (nb068AlphaDummy434 f) from (by
                                unfold nb068AlphaDummy434;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0441 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy429), (nb068AlphaDummy432 f)),
          ((nb068AlphaDummy428), (nb068AlphaDummy431 f)),
          ((nb068AlphaDummy427), (nb068AlphaDummy430 f)),
          ((nb068AlphaDummy425), (nb068AlphaDummy426 f)),
          ((nb068AlphaDummy421), (nb068AlphaDummy423 f)),
          ((nb068AlphaDummy422), (nb068AlphaDummy424 f)),
          ((nb068AlphaDummy447), (nb068AlphaDummy448 f)),
          ((nb068AlphaDummy445), (nb068AlphaDummy446 f)),
          ((nb068AlphaDummy414), (nb068AlphaDummy416 f)),
          ((nb068AlphaDummy413), (nb068AlphaDummy415 f)),
          ((nb068AlphaDummy443), (nb068AlphaDummy444 f)),
          ((nb068AlphaDummy417), (nb068AlphaDummy418 f)),
          ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
          ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
          ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
          ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy428) ≠ (nb068AlphaDummy439) from (by
                                unfold nb068AlphaDummy439;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0446) 0))))
                            (show (nb068AlphaDummy431 f) ≠ (nb068AlphaDummy440 f) from (by
                                unfold nb068AlphaDummy440;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0447 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy428) ≠ (nb068AlphaDummy437) from (by
                                  unfold nb068AlphaDummy437;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0444) 0))))
                              (show (nb068AlphaDummy431 f) ≠ (nb068AlphaDummy438 f) from
                                (by
                                  unfold nb068AlphaDummy438;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0445 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy428) ≠ (nb068AlphaDummy439) from (by
                                unfold nb068AlphaDummy439;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0446) 0))))
                            (show (nb068AlphaDummy431 f) ≠ (nb068AlphaDummy440 f) from (by
                                unfold nb068AlphaDummy440;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0447 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy428) ≠ (nb068AlphaDummy437) from (by
                                  unfold nb068AlphaDummy437;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0444) 0))))
                              (show (nb068AlphaDummy431 f) ≠ (nb068AlphaDummy438 f) from
                                (by
                                  unfold nb068AlphaDummy438;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0445 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy429) ≠ (nb068AlphaDummy441) from (by
                                unfold nb068AlphaDummy441;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0450) 0))))
                            (show (nb068AlphaDummy432 f) ≠ (nb068AlphaDummy442 f) from (by
                                unfold nb068AlphaDummy442;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0451 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy429) ≠ (nb068AlphaDummy437) from (by
                                  unfold nb068AlphaDummy437;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0448) 0))))
                              (show (nb068AlphaDummy432 f) ≠ (nb068AlphaDummy438 f) from
                                (by
                                  unfold nb068AlphaDummy438;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0449 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy429) ≠ (nb068AlphaDummy441) from (by
                                unfold nb068AlphaDummy441;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0450) 0))))
                            (show (nb068AlphaDummy432 f) ≠ (nb068AlphaDummy442 f) from (by
                                unfold nb068AlphaDummy442;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0451 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy429) ≠ (nb068AlphaDummy437) from (by
                                  unfold nb068AlphaDummy437;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0448) 0))))
                              (show (nb068AlphaDummy432 f) ≠ (nb068AlphaDummy438 f) from
                                (by
                                  unfold nb068AlphaDummy438;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0449 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0102`. -/
@[expose]
noncomputable def nb068SplitAlpha0102 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy425), (nb068AlphaDummy426 f)),
        ((nb068AlphaDummy421), (nb068AlphaDummy423 f)),
        ((nb068AlphaDummy422), (nb068AlphaDummy424 f)),
        ((nb068AlphaDummy447), (nb068AlphaDummy448 f)),
        ((nb068AlphaDummy445), (nb068AlphaDummy446 f)),
        ((nb068AlphaDummy414), (nb068AlphaDummy416 f)),
        ((nb068AlphaDummy413), (nb068AlphaDummy415 f)),
        ((nb068AlphaDummy443), (nb068AlphaDummy444 f)),
        ((nb068AlphaDummy417), (nb068AlphaDummy418 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy425))
              (synCplc (Class.cv (nb068AlphaDummy421)) (synC1c)))
            (Wff.classMem (Class.cv (nb068AlphaDummy421)) (synCnnc)))) (synWa
          (Wff.classMem (Class.cv (nb068AlphaDummy425)) (Class.cv (nb068AlphaDummy421)))
          (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy421)) (synCnnc)))))
      (Wff.imp (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy426 f))
              (synCplc (Class.cv (nb068AlphaDummy423 f)) (synC1c)))
            (Wff.classMem (Class.cv (nb068AlphaDummy423 f)) (synCnnc)))) (synWa
          (Wff.classMem (Class.cv (nb068AlphaDummy426 f))
            (Class.cv (nb068AlphaDummy423 f)))
          (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy423 f)) (synCnnc))))) :=
  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy421) ≠ (nb068AlphaDummy428) from (by
                          unfold nb068AlphaDummy428;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0434) 1))))
                      (show (nb068AlphaDummy423 f) ≠ (nb068AlphaDummy431 f) from (by
                          unfold nb068AlphaDummy431;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0435 f) 1))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy421) ≠ (nb068AlphaDummy427) from (by
                            unfold nb068AlphaDummy427;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0434) 0))))
                        (show (nb068AlphaDummy423 f) ≠ (nb068AlphaDummy430 f) from (by
                            unfold nb068AlphaDummy430;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0435 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy421) ≠ (nb068AlphaDummy425) from (by
                              unfold nb068AlphaDummy425;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0432) 0))))
                          (show (nb068AlphaDummy423 f) ≠ (nb068AlphaDummy426 f) from (by
                              unfold nb068AlphaDummy426;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0433 f) 0))))
                          (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy429), (nb068AlphaDummy432 f)),
                          ((nb068AlphaDummy428), (nb068AlphaDummy431 f)),
                          ((nb068AlphaDummy427), (nb068AlphaDummy430 f)),
                          ((nb068AlphaDummy425), (nb068AlphaDummy426 f)),
                          ((nb068AlphaDummy421), (nb068AlphaDummy423 f)),
                          ((nb068AlphaDummy422), (nb068AlphaDummy424 f)),
                          ((nb068AlphaDummy447), (nb068AlphaDummy448 f)),
                          ((nb068AlphaDummy445), (nb068AlphaDummy446 f)),
                          ((nb068AlphaDummy414), (nb068AlphaDummy416 f)),
                          ((nb068AlphaDummy413), (nb068AlphaDummy415 f)),
                          ((nb068AlphaDummy443), (nb068AlphaDummy444 f)),
                          ((nb068AlphaDummy417), (nb068AlphaDummy418 f)),
                          ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                          ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                          ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                          ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                          ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synC1c) (by simp only [fv_syn_c1c])))
                    (TAlphaWff.neg (nb068SplitAlpha0101 x y f)))))))) (TAlphaWff.classMem
          (TAlphaClass.cv (TAlphaVar.there
              (show (nb068AlphaDummy421) ≠ (nb068AlphaDummy425) from (by
                  unfold nb068AlphaDummy425;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0432) 0))))
              (show (nb068AlphaDummy423 f) ≠ (nb068AlphaDummy426 f) from (by
                  unfold nb068AlphaDummy426;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0433 f) 0))))
              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
            [((nb068AlphaDummy425), (nb068AlphaDummy426 f)),
              ((nb068AlphaDummy421), (nb068AlphaDummy423 f)),
              ((nb068AlphaDummy422), (nb068AlphaDummy424 f)),
              ((nb068AlphaDummy447), (nb068AlphaDummy448 f)),
              ((nb068AlphaDummy445), (nb068AlphaDummy446 f)),
              ((nb068AlphaDummy414), (nb068AlphaDummy416 f)),
              ((nb068AlphaDummy413), (nb068AlphaDummy415 f)),
              ((nb068AlphaDummy443), (nb068AlphaDummy444 f)),
              ((nb068AlphaDummy417), (nb068AlphaDummy418 f)),
              ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
              ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
              ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
              ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
              ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
              ((nb068AlphaDummy001), x),
              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (show (nb068AlphaDummy421) ≠ (nb068AlphaDummy425) from (by
                unfold nb068AlphaDummy425;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0432) 0))))
            (show (nb068AlphaDummy423 f) ≠ (nb068AlphaDummy426 f) from (by
                unfold nb068AlphaDummy426;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0433 f) 0))))
            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
            (TAlphaVar.there (show (nb068AlphaDummy421) ≠ (nb068AlphaDummy425) from (by
                  unfold nb068AlphaDummy425;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0432) 0))))
              (show (nb068AlphaDummy423 f) ≠ (nb068AlphaDummy426 f) from (by
                  unfold nb068AlphaDummy426;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0433 f) 0))))
              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
            [((nb068AlphaDummy425), (nb068AlphaDummy426 f)),
              ((nb068AlphaDummy421), (nb068AlphaDummy423 f)),
              ((nb068AlphaDummy422), (nb068AlphaDummy424 f)),
              ((nb068AlphaDummy447), (nb068AlphaDummy448 f)),
              ((nb068AlphaDummy445), (nb068AlphaDummy446 f)),
              ((nb068AlphaDummy414), (nb068AlphaDummy416 f)),
              ((nb068AlphaDummy413), (nb068AlphaDummy415 f)),
              ((nb068AlphaDummy443), (nb068AlphaDummy444 f)),
              ((nb068AlphaDummy417), (nb068AlphaDummy418 f)),
              ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
              ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
              ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
              ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
              ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
              ((nb068AlphaDummy001), x),
              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
            (synCnnc) (by simp only [fv_syn_cnnc]))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0103`. -/
@[expose]
noncomputable def nb068SplitAlpha0103 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy443), (nb068AlphaDummy444 f)),
        ((nb068AlphaDummy417), (nb068AlphaDummy418 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy443))
          (Class.cab (nb068AlphaDummy413)
            (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy408))
              (Wff.classEq (Class.cv (nb068AlphaDummy413))
                (synCun (synCphi (Class.cv (nb068AlphaDummy414))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy443))
            (Class.cab (nb068AlphaDummy413)
              (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy408))
                (Wff.classEq (Class.cv (nb068AlphaDummy413))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy414)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy444 f))
          (Class.cab (nb068AlphaDummy415 f)
            (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy410 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy416 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy444 f))
            (Class.cab (nb068AlphaDummy415 f)
              (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy410 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy416 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy408) ≠ (nb068AlphaDummy414) from
                    (by
                      unfold nb068AlphaDummy414;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0452) 1))))
                  (show (nb068AlphaDummy410 f) ≠ (nb068AlphaDummy416 f) from (by
                      unfold nb068AlphaDummy416;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0454 f) 1))))
                  (TAlphaVar.there (show (nb068AlphaDummy408) ≠ (nb068AlphaDummy413) from
                      (by
                        unfold nb068AlphaDummy413;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0452) 0))))
                    (show (nb068AlphaDummy410 f) ≠ (nb068AlphaDummy415 f) from (by
                        unfold nb068AlphaDummy415;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0454 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy408) ≠ (nb068AlphaDummy443) from (by
                          unfold nb068AlphaDummy443;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0456) 0))))
                      (show (nb068AlphaDummy410 f) ≠ (nb068AlphaDummy444 f) from (by
                          unfold nb068AlphaDummy444;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0457 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy408) ≠ (nb068AlphaDummy417) from (by
                            unfold nb068AlphaDummy417;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0453) 0))))
                        (show (nb068AlphaDummy410 f) ≠ (nb068AlphaDummy418 f) from (by
                            unfold nb068AlphaDummy418;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0455 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy407))).fv ∪
                      ((Class.cv (nb068AlphaDummy408))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068AlphaDummy409 f))).fv ∪
                      ((Class.cv (nb068AlphaDummy410 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb068AlphaDummy414) ≠
        (nb068AlphaDummy421) from (by
          unfold nb068AlphaDummy421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0430) 0)))) (show (nb068AlphaDummy416 f) ≠
        (nb068AlphaDummy423 f) from (by
          unfold nb068AlphaDummy423;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0431 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy414) ≠ (nb068AlphaDummy422) from (by
          unfold nb068AlphaDummy422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0430) 1)))) (show (nb068AlphaDummy416 f) ≠
        (nb068AlphaDummy424 f) from (by
          unfold nb068AlphaDummy424;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0431 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy414) ≠ (nb068AlphaDummy447) from (by
          unfold nb068AlphaDummy447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0460) 0)))) (show (nb068AlphaDummy416 f) ≠
        (nb068AlphaDummy448 f) from (by
          unfold nb068AlphaDummy448;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0461 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy414) ≠ (nb068AlphaDummy445) from (by
          unfold nb068AlphaDummy445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0458) 0)))) (show (nb068AlphaDummy416 f) ≠
        (nb068AlphaDummy446 f) from (by
          unfold nb068AlphaDummy446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0459 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068AlphaDummy414))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb068AlphaDummy416 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (nb068SplitAlpha0102 x y f)))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb068AlphaDummy414) ≠
        (nb068AlphaDummy421) from (by
          unfold nb068AlphaDummy421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0430) 0)))) (show (nb068AlphaDummy416 f) ≠
        (nb068AlphaDummy423 f) from (by
          unfold nb068AlphaDummy423;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0431 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy414) ≠ (nb068AlphaDummy422) from (by
          unfold nb068AlphaDummy422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0430) 1)))) (show (nb068AlphaDummy416 f) ≠
        (nb068AlphaDummy424 f) from (by
          unfold nb068AlphaDummy424;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0431 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy414) ≠ (nb068AlphaDummy447) from (by
          unfold nb068AlphaDummy447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0460) 0)))) (show (nb068AlphaDummy416 f) ≠
        (nb068AlphaDummy448 f) from (by
          unfold nb068AlphaDummy448;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0461 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy414) ≠ (nb068AlphaDummy445) from (by
          unfold nb068AlphaDummy445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0458) 0)))) (show (nb068AlphaDummy416 f) ≠
        (nb068AlphaDummy446 f) from (by
          unfold nb068AlphaDummy446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0459 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068AlphaDummy414))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb068AlphaDummy416 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (nb068SplitAlpha0102 x y f)))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy445), (nb068AlphaDummy446 f)),
                          ((nb068AlphaDummy414), (nb068AlphaDummy416 f)),
                          ((nb068AlphaDummy413), (nb068AlphaDummy415 f)),
                          ((nb068AlphaDummy443), (nb068AlphaDummy444 f)),
                          ((nb068AlphaDummy417), (nb068AlphaDummy418 f)),
                          ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                          ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                          ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                          ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                          ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy408) ≠ (nb068AlphaDummy414) from
                      (by
                        unfold nb068AlphaDummy414;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0452) 1))))
                    (show (nb068AlphaDummy410 f) ≠ (nb068AlphaDummy416 f) from (by
                        unfold nb068AlphaDummy416;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0454 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy408) ≠ (nb068AlphaDummy413) from (by
                          unfold nb068AlphaDummy413;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0452) 0))))
                      (show (nb068AlphaDummy410 f) ≠ (nb068AlphaDummy415 f) from (by
                          unfold nb068AlphaDummy415;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0454 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy408) ≠ (nb068AlphaDummy443) from (by
                            unfold nb068AlphaDummy443;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0456) 0))))
                        (show (nb068AlphaDummy410 f) ≠ (nb068AlphaDummy444 f) from (by
                            unfold nb068AlphaDummy444;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0457 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy408) ≠ (nb068AlphaDummy417) from (by
                              unfold nb068AlphaDummy417;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0453) 0))))
                          (show (nb068AlphaDummy410 f) ≠ (nb068AlphaDummy418 f) from (by
                              unfold nb068AlphaDummy418;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0455 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068AlphaDummy407))).fv ∪
                        ((Class.cv (nb068AlphaDummy408))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy409 f))).fv ∪
                        ((Class.cv (nb068AlphaDummy410 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy414) ≠ (nb068AlphaDummy421) from (by
          unfold nb068AlphaDummy421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0430) 0)))) (show (nb068AlphaDummy416 f) ≠
        (nb068AlphaDummy423 f) from (by
          unfold nb068AlphaDummy423;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0431 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy414) ≠ (nb068AlphaDummy422) from (by
          unfold nb068AlphaDummy422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0430) 1)))) (show (nb068AlphaDummy416 f) ≠
        (nb068AlphaDummy424 f) from (by
          unfold nb068AlphaDummy424;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0431 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy414) ≠ (nb068AlphaDummy447) from (by
          unfold nb068AlphaDummy447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0460) 0)))) (show (nb068AlphaDummy416 f) ≠
        (nb068AlphaDummy448 f) from (by
          unfold nb068AlphaDummy448;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0461 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy414) ≠ (nb068AlphaDummy445)
        from (by
          unfold nb068AlphaDummy445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0458)
                  0)))) (show (nb068AlphaDummy416 f) ≠ (nb068AlphaDummy446 f) from (by
          unfold nb068AlphaDummy446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0459 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy414))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb068AlphaDummy416 f))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb068SplitAlpha0102 x y f)))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy414) ≠ (nb068AlphaDummy421) from (by
          unfold nb068AlphaDummy421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0430) 0)))) (show (nb068AlphaDummy416 f) ≠
        (nb068AlphaDummy423 f) from (by
          unfold nb068AlphaDummy423;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0431 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy414) ≠ (nb068AlphaDummy422) from (by
          unfold nb068AlphaDummy422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0430) 1)))) (show (nb068AlphaDummy416 f) ≠
        (nb068AlphaDummy424 f) from (by
          unfold nb068AlphaDummy424;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0431 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy414) ≠ (nb068AlphaDummy447) from (by
          unfold nb068AlphaDummy447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0460) 0)))) (show (nb068AlphaDummy416 f) ≠
        (nb068AlphaDummy448 f) from (by
          unfold nb068AlphaDummy448;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0461 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy414) ≠ (nb068AlphaDummy445)
        from (by
          unfold nb068AlphaDummy445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0458)
                  0)))) (show (nb068AlphaDummy416 f) ≠ (nb068AlphaDummy446 f) from (by
          unfold nb068AlphaDummy446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0459 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy414))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb068AlphaDummy416 f))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb068SplitAlpha0102 x y f)))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy445), (nb068AlphaDummy446 f)),
                            ((nb068AlphaDummy414), (nb068AlphaDummy416 f)),
                            ((nb068AlphaDummy413), (nb068AlphaDummy415 f)),
                            ((nb068AlphaDummy443), (nb068AlphaDummy444 f)),
                            ((nb068AlphaDummy417), (nb068AlphaDummy418 f)),
                            ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                            ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                            ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                            ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                            ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                            ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                            ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                            ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                            ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                            ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                            ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part042`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0104`. -/
@[expose]
noncomputable def nb068SplitAlpha0104 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy465), (nb068AlphaDummy468 f)),
        ((nb068AlphaDummy464), (nb068AlphaDummy467 f)),
        ((nb068AlphaDummy463), (nb068AlphaDummy466 f)),
        ((nb068AlphaDummy461), (nb068AlphaDummy462 f)),
        ((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
        ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
        ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
        ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
        ((nb068AlphaDummy455), (nb068AlphaDummy456 f)),
        ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy464)) (Class.cv (nb068AlphaDummy465)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy463))
            (synCun (Class.cv (nb068AlphaDummy464)) (Class.cv (nb068AlphaDummy465))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy467 f))
            (Class.cv (nb068AlphaDummy468 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy466 f))
            (synCun (Class.cv (nb068AlphaDummy467 f))
              (Class.cv (nb068AlphaDummy468 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy471) from (by
                              unfold nb068AlphaDummy471;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0476) 0))))
                          (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy472 f) from (by
                              unfold nb068AlphaDummy472;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0477 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy469) from (by
                                unfold nb068AlphaDummy469;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0474) 0))))
                            (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy470 f) from (by
                                unfold nb068AlphaDummy470;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0475 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy471) from (by
                              unfold nb068AlphaDummy471;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0480) 0))))
                          (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy472 f) from (by
                              unfold nb068AlphaDummy472;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0481 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy469) from (by
                                unfold nb068AlphaDummy469;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0478) 0))))
                            (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy470 f) from (by
                                unfold nb068AlphaDummy470;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0479 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy471) from (by
                              unfold nb068AlphaDummy471;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0476) 0))))
                          (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy472 f) from (by
                              unfold nb068AlphaDummy472;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0477 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy469) from (by
                                unfold nb068AlphaDummy469;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0474) 0))))
                            (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy470 f) from (by
                                unfold nb068AlphaDummy470;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0475 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy471) from (by
                              unfold nb068AlphaDummy471;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0480) 0))))
                          (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy472 f) from (by
                              unfold nb068AlphaDummy472;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0481 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy469) from (by
                                unfold nb068AlphaDummy469;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0478) 0))))
                            (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy470 f) from (by
                                unfold nb068AlphaDummy470;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0479 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy465), (nb068AlphaDummy468 f)),
          ((nb068AlphaDummy464), (nb068AlphaDummy467 f)),
          ((nb068AlphaDummy463), (nb068AlphaDummy466 f)),
          ((nb068AlphaDummy461), (nb068AlphaDummy462 f)),
          ((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
          ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
          ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
          ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
          ((nb068AlphaDummy455), (nb068AlphaDummy456 f)),
          ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
          ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
          ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
          ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
          ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy475) from (by
                                unfold nb068AlphaDummy475;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0484) 0))))
                            (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy476 f) from (by
                                unfold nb068AlphaDummy476;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0485 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy473) from (by
                                  unfold nb068AlphaDummy473;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0482) 0))))
                              (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy474 f) from
                                (by
                                  unfold nb068AlphaDummy474;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0483 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy475) from (by
                                unfold nb068AlphaDummy475;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0484) 0))))
                            (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy476 f) from (by
                                unfold nb068AlphaDummy476;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0485 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy473) from (by
                                  unfold nb068AlphaDummy473;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0482) 0))))
                              (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy474 f) from
                                (by
                                  unfold nb068AlphaDummy474;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0483 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy477) from (by
                                unfold nb068AlphaDummy477;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0488) 0))))
                            (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy478 f) from (by
                                unfold nb068AlphaDummy478;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0489 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy473) from (by
                                  unfold nb068AlphaDummy473;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0486) 0))))
                              (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy474 f) from
                                (by
                                  unfold nb068AlphaDummy474;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0487 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy477) from (by
                                unfold nb068AlphaDummy477;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0488) 0))))
                            (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy478 f) from (by
                                unfold nb068AlphaDummy478;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0489 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy473) from (by
                                  unfold nb068AlphaDummy473;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0486) 0))))
                              (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy474 f) from
                                (by
                                  unfold nb068AlphaDummy474;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0487 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0105`. -/
@[expose]
noncomputable def nb068SplitAlpha0105 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
        ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
        ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
        ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
        ((nb068AlphaDummy455), (nb068AlphaDummy456 f)),
        ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classEq (Class.cv (nb068AlphaDummy458))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy457)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy457)) (synC1c))
          (Class.cv (nb068AlphaDummy457))))
      (Wff.classEq (Class.cv (nb068AlphaDummy460 f))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy459 f)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy459 f)) (synC1c))
          (Class.cv (nb068AlphaDummy459 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068AlphaDummy450))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb068AlphaDummy452 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy464) from (by
                              unfold nb068AlphaDummy464;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0472) 1))))
                          (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy467 f) from (by
                              unfold nb068AlphaDummy467;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0473 f) 1))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy463) from (by
                                unfold nb068AlphaDummy463;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0472) 0))))
                            (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy466 f) from (by
                                unfold nb068AlphaDummy466;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0473 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy461) from (by
                                  unfold nb068AlphaDummy461;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0470) 0))))
                              (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy462 f) from
                                (by
                                  unfold nb068AlphaDummy462;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0471 f) 0))))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb068AlphaDummy465), (nb068AlphaDummy468 f)),
                              ((nb068AlphaDummy464), (nb068AlphaDummy467 f)),
                              ((nb068AlphaDummy463), (nb068AlphaDummy466 f)),
                              ((nb068AlphaDummy461), (nb068AlphaDummy462 f)),
                              ((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
                              ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
                              ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
                              ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
                              ((nb068AlphaDummy455), (nb068AlphaDummy456 f)),
                              ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
                              ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                              ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                              ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                              ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                              ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                              ((nb068AlphaDummy001), x),
                              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                            (synC1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb068SplitAlpha0104 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy461) from (by
                      unfold nb068AlphaDummy461;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0470) 0))))
                  (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy462 f) from (by
                      unfold nb068AlphaDummy462;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0471 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb068AlphaDummy461), (nb068AlphaDummy462 f)),
                  ((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
                  ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
                  ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
                  ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
                  ((nb068AlphaDummy455), (nb068AlphaDummy456 f)),
                  ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
                  ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                  ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                  ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                  ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                  ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                  ((nb068AlphaDummy001), x),
                  ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy461) from (by
                    unfold nb068AlphaDummy461;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0470) 0))))
                (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy462 f) from (by
                    unfold nb068AlphaDummy462;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0471 f) 0))))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy461) from
                    (by
                      unfold nb068AlphaDummy461;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0470) 0))))
                  (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy462 f) from (by
                      unfold nb068AlphaDummy462;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0471 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb068AlphaDummy461), (nb068AlphaDummy462 f)),
                  ((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
                  ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
                  ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
                  ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
                  ((nb068AlphaDummy455), (nb068AlphaDummy456 f)),
                  ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
                  ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                  ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                  ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                  ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                  ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                  ((nb068AlphaDummy001), x),
                  ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0106`. -/
@[expose]
noncomputable def nb068SplitAlpha0106 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy465), (nb068AlphaDummy468 f)),
        ((nb068AlphaDummy464), (nb068AlphaDummy467 f)),
        ((nb068AlphaDummy463), (nb068AlphaDummy466 f)),
        ((nb068AlphaDummy461), (nb068AlphaDummy462 f)),
        ((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
        ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
        ((nb068AlphaDummy483), (nb068AlphaDummy484 f)),
        ((nb068AlphaDummy481), (nb068AlphaDummy482 f)),
        ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
        ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
        ((nb068AlphaDummy479), (nb068AlphaDummy480 f)),
        ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy464)) (Class.cv (nb068AlphaDummy465)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy463))
            (synCun (Class.cv (nb068AlphaDummy464)) (Class.cv (nb068AlphaDummy465))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy467 f))
            (Class.cv (nb068AlphaDummy468 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy466 f))
            (synCun (Class.cv (nb068AlphaDummy467 f))
              (Class.cv (nb068AlphaDummy468 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy471) from (by
                              unfold nb068AlphaDummy471;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0476) 0))))
                          (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy472 f) from (by
                              unfold nb068AlphaDummy472;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0477 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy469) from (by
                                unfold nb068AlphaDummy469;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0474) 0))))
                            (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy470 f) from (by
                                unfold nb068AlphaDummy470;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0475 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy471) from (by
                              unfold nb068AlphaDummy471;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0480) 0))))
                          (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy472 f) from (by
                              unfold nb068AlphaDummy472;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0481 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy469) from (by
                                unfold nb068AlphaDummy469;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0478) 0))))
                            (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy470 f) from (by
                                unfold nb068AlphaDummy470;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0479 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy471) from (by
                              unfold nb068AlphaDummy471;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0476) 0))))
                          (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy472 f) from (by
                              unfold nb068AlphaDummy472;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0477 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy469) from (by
                                unfold nb068AlphaDummy469;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0474) 0))))
                            (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy470 f) from (by
                                unfold nb068AlphaDummy470;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0475 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy471) from (by
                              unfold nb068AlphaDummy471;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0480) 0))))
                          (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy472 f) from (by
                              unfold nb068AlphaDummy472;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0481 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy469) from (by
                                unfold nb068AlphaDummy469;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0478) 0))))
                            (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy470 f) from (by
                                unfold nb068AlphaDummy470;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0479 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy465), (nb068AlphaDummy468 f)),
          ((nb068AlphaDummy464), (nb068AlphaDummy467 f)),
          ((nb068AlphaDummy463), (nb068AlphaDummy466 f)),
          ((nb068AlphaDummy461), (nb068AlphaDummy462 f)),
          ((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
          ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
          ((nb068AlphaDummy483), (nb068AlphaDummy484 f)),
          ((nb068AlphaDummy481), (nb068AlphaDummy482 f)),
          ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
          ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
          ((nb068AlphaDummy479), (nb068AlphaDummy480 f)),
          ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
          ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
          ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
          ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
          ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy475) from (by
                                unfold nb068AlphaDummy475;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0484) 0))))
                            (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy476 f) from (by
                                unfold nb068AlphaDummy476;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0485 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy473) from (by
                                  unfold nb068AlphaDummy473;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0482) 0))))
                              (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy474 f) from
                                (by
                                  unfold nb068AlphaDummy474;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0483 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy475) from (by
                                unfold nb068AlphaDummy475;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0484) 0))))
                            (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy476 f) from (by
                                unfold nb068AlphaDummy476;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0485 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy473) from (by
                                  unfold nb068AlphaDummy473;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0482) 0))))
                              (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy474 f) from
                                (by
                                  unfold nb068AlphaDummy474;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0483 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy477) from (by
                                unfold nb068AlphaDummy477;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0488) 0))))
                            (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy478 f) from (by
                                unfold nb068AlphaDummy478;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0489 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy473) from (by
                                  unfold nb068AlphaDummy473;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0486) 0))))
                              (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy474 f) from
                                (by
                                  unfold nb068AlphaDummy474;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0487 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy477) from (by
                                unfold nb068AlphaDummy477;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0488) 0))))
                            (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy478 f) from (by
                                unfold nb068AlphaDummy478;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0489 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy473) from (by
                                  unfold nb068AlphaDummy473;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0486) 0))))
                              (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy474 f) from
                                (by
                                  unfold nb068AlphaDummy474;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0487 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0107`. -/
@[expose]
noncomputable def nb068SplitAlpha0107 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy461), (nb068AlphaDummy462 f)),
        ((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
        ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
        ((nb068AlphaDummy483), (nb068AlphaDummy484 f)),
        ((nb068AlphaDummy481), (nb068AlphaDummy482 f)),
        ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
        ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
        ((nb068AlphaDummy479), (nb068AlphaDummy480 f)),
        ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy461))
              (synCplc (Class.cv (nb068AlphaDummy457)) (synC1c)))
            (Wff.classMem (Class.cv (nb068AlphaDummy457)) (synCnnc)))) (synWa
          (Wff.classMem (Class.cv (nb068AlphaDummy461)) (Class.cv (nb068AlphaDummy457)))
          (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy457)) (synCnnc)))))
      (Wff.imp (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy462 f))
              (synCplc (Class.cv (nb068AlphaDummy459 f)) (synC1c)))
            (Wff.classMem (Class.cv (nb068AlphaDummy459 f)) (synCnnc)))) (synWa
          (Wff.classMem (Class.cv (nb068AlphaDummy462 f))
            (Class.cv (nb068AlphaDummy459 f)))
          (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy459 f)) (synCnnc))))) :=
  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy464) from (by
                          unfold nb068AlphaDummy464;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0472) 1))))
                      (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy467 f) from (by
                          unfold nb068AlphaDummy467;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0473 f) 1))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy463) from (by
                            unfold nb068AlphaDummy463;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0472) 0))))
                        (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy466 f) from (by
                            unfold nb068AlphaDummy466;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0473 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy461) from (by
                              unfold nb068AlphaDummy461;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0470) 0))))
                          (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy462 f) from (by
                              unfold nb068AlphaDummy462;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0471 f) 0))))
                          (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy465), (nb068AlphaDummy468 f)),
                          ((nb068AlphaDummy464), (nb068AlphaDummy467 f)),
                          ((nb068AlphaDummy463), (nb068AlphaDummy466 f)),
                          ((nb068AlphaDummy461), (nb068AlphaDummy462 f)),
                          ((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
                          ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
                          ((nb068AlphaDummy483), (nb068AlphaDummy484 f)),
                          ((nb068AlphaDummy481), (nb068AlphaDummy482 f)),
                          ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
                          ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
                          ((nb068AlphaDummy479), (nb068AlphaDummy480 f)),
                          ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
                          ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                          ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                          ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                          ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                          ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synC1c) (by simp only [fv_syn_c1c])))
                    (TAlphaWff.neg (nb068SplitAlpha0106 x y f)))))))) (TAlphaWff.classMem
          (TAlphaClass.cv (TAlphaVar.there
              (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy461) from (by
                  unfold nb068AlphaDummy461;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0470) 0))))
              (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy462 f) from (by
                  unfold nb068AlphaDummy462;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0471 f) 0))))
              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
            [((nb068AlphaDummy461), (nb068AlphaDummy462 f)),
              ((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
              ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
              ((nb068AlphaDummy483), (nb068AlphaDummy484 f)),
              ((nb068AlphaDummy481), (nb068AlphaDummy482 f)),
              ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
              ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
              ((nb068AlphaDummy479), (nb068AlphaDummy480 f)),
              ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
              ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
              ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
              ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
              ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
              ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
              ((nb068AlphaDummy001), x),
              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy461) from (by
                unfold nb068AlphaDummy461;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0470) 0))))
            (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy462 f) from (by
                unfold nb068AlphaDummy462;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0471 f) 0))))
            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
            (TAlphaVar.there (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy461) from (by
                  unfold nb068AlphaDummy461;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0470) 0))))
              (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy462 f) from (by
                  unfold nb068AlphaDummy462;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0471 f) 0))))
              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
            [((nb068AlphaDummy461), (nb068AlphaDummy462 f)),
              ((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
              ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
              ((nb068AlphaDummy483), (nb068AlphaDummy484 f)),
              ((nb068AlphaDummy481), (nb068AlphaDummy482 f)),
              ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
              ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
              ((nb068AlphaDummy479), (nb068AlphaDummy480 f)),
              ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
              ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
              ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
              ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
              ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
              ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
              ((nb068AlphaDummy001), x),
              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
            (synCnnc) (by simp only [fv_syn_cnnc]))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
