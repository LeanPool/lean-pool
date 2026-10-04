/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C068C001Block009

/-! NF weak partition development: NAR4C068C001Part036. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0085`. -/
@[expose]
noncomputable def nb068SplitAlpha0085 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
        ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
        ((nb068AlphaDummy293), (nb068AlphaDummy294 f)),
        ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
        ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
        ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classEq (Class.cv (nb068AlphaDummy287))
        (synCphi (Class.cv (nb068AlphaDummy288))))
      (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
        (synCphi (Class.cv (nb068AlphaDummy290 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb068AlphaDummy284))).fv ∪ ((Class.cv (nb068AlphaDummy283))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb068AlphaDummy286 f))).fv ∪
            ((Class.cv (nb068AlphaDummy285 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068AlphaDummy288) ≠ (nb068AlphaDummy295) from (by
                    unfold nb068AlphaDummy295;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0298) 0))))
                (show (nb068AlphaDummy290 f) ≠ (nb068AlphaDummy297 f) from (by
                    unfold nb068AlphaDummy297;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0299 f) 0))))
                (TAlphaVar.there (show (nb068AlphaDummy288) ≠ (nb068AlphaDummy296) from
                    (by
                      unfold nb068AlphaDummy296;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0298) 1))))
                  (show (nb068AlphaDummy290 f) ≠ (nb068AlphaDummy298 f) from (by
                      unfold nb068AlphaDummy298;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0299 f) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb068AlphaDummy288))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb068AlphaDummy290 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy295) ≠ (nb068AlphaDummy302) from
                                    (by
                                      unfold nb068AlphaDummy302;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0302)
                                              1)))) (show
                                    (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy305 f) from
                                    (by
                                      unfold nb068AlphaDummy305;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0303 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy295) ≠ (nb068AlphaDummy301) from (by
                                        unfold nb068AlphaDummy301;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0302)
                                                0)))) (show (nb068AlphaDummy297 f) ≠
                                        (nb068AlphaDummy304 f) from (by
                                        unfold nb068AlphaDummy304;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0303 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy295) ≠ (nb068AlphaDummy299) from
                                        (by
                                          unfold nb068AlphaDummy299;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0300)
                                                  0)))) (show (nb068AlphaDummy297 f) ≠
        (nb068AlphaDummy300 f) from (by
                                          unfold nb068AlphaDummy300;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0301 f) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [((nb068AlphaDummy303), (nb068AlphaDummy306 f)),
                                      ((nb068AlphaDummy302), (nb068AlphaDummy305 f)),
                                      ((nb068AlphaDummy301), (nb068AlphaDummy304 f)),
                                      ((nb068AlphaDummy299), (nb068AlphaDummy300 f)),
                                      ((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
                                      ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
                                      ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
                                      ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
                                      ((nb068AlphaDummy293), (nb068AlphaDummy294 f)),
                                      ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
                                      ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
                                      ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
                                      ((nb068AlphaDummy000), f),
                                      ((nb068AlphaDummy002), y),
                                      ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                        (nb068AlphaDummy004 x y f))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb068SplitAlpha0084 x y f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068AlphaDummy295) ≠ (nb068AlphaDummy299) from (by
                              unfold nb068AlphaDummy299;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                          (show (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy300 f) from (by
                              unfold nb068AlphaDummy300;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy299), (nb068AlphaDummy300 f)),
                          ((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
                          ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
                          ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
                          ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
                          ((nb068AlphaDummy293), (nb068AlphaDummy294 f)),
                          ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
                          ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
                          ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb068AlphaDummy295) ≠ (nb068AlphaDummy299) from (by
                            unfold nb068AlphaDummy299;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                        (show (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy300 f) from (by
                            unfold nb068AlphaDummy300;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068AlphaDummy295) ≠ (nb068AlphaDummy299) from (by
                              unfold nb068AlphaDummy299;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                          (show (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy300 f) from (by
                              unfold nb068AlphaDummy300;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy299), (nb068AlphaDummy300 f)),
                          ((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
                          ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
                          ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
                          ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
                          ((nb068AlphaDummy293), (nb068AlphaDummy294 f)),
                          ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
                          ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
                          ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0086`. -/
@[expose]
noncomputable def nb068SplitAlpha0086 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy303), (nb068AlphaDummy306 f)),
        ((nb068AlphaDummy302), (nb068AlphaDummy305 f)),
        ((nb068AlphaDummy301), (nb068AlphaDummy304 f)),
        ((nb068AlphaDummy299), (nb068AlphaDummy300 f)),
        ((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
        ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
        ((nb068AlphaDummy321), (nb068AlphaDummy322 f)),
        ((nb068AlphaDummy319), (nb068AlphaDummy320 f)),
        ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
        ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
        ((nb068AlphaDummy317), (nb068AlphaDummy318 f)),
        ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
        ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
        ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy302)) (Class.cv (nb068AlphaDummy303)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy301))
            (synCun (Class.cv (nb068AlphaDummy302)) (Class.cv (nb068AlphaDummy303))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy305 f))
            (Class.cv (nb068AlphaDummy306 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy304 f))
            (synCun (Class.cv (nb068AlphaDummy305 f))
              (Class.cv (nb068AlphaDummy306 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy309) from (by
                              unfold nb068AlphaDummy309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0306) 0))))
                          (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy310 f) from (by
                              unfold nb068AlphaDummy310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0307 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy307) from (by
                                unfold nb068AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0304) 0))))
                            (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy308 f) from (by
                                unfold nb068AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0305 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy309) from (by
                              unfold nb068AlphaDummy309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0310) 0))))
                          (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy310 f) from (by
                              unfold nb068AlphaDummy310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0311 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy307) from (by
                                unfold nb068AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0308) 0))))
                            (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy308 f) from (by
                                unfold nb068AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0309 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy309) from (by
                              unfold nb068AlphaDummy309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0306) 0))))
                          (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy310 f) from (by
                              unfold nb068AlphaDummy310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0307 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy307) from (by
                                unfold nb068AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0304) 0))))
                            (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy308 f) from (by
                                unfold nb068AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0305 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy309) from (by
                              unfold nb068AlphaDummy309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0310) 0))))
                          (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy310 f) from (by
                              unfold nb068AlphaDummy310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0311 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy307) from (by
                                unfold nb068AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0308) 0))))
                            (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy308 f) from (by
                                unfold nb068AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0309 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy303), (nb068AlphaDummy306 f)),
          ((nb068AlphaDummy302), (nb068AlphaDummy305 f)),
          ((nb068AlphaDummy301), (nb068AlphaDummy304 f)),
          ((nb068AlphaDummy299), (nb068AlphaDummy300 f)),
          ((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
          ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
          ((nb068AlphaDummy321), (nb068AlphaDummy322 f)),
          ((nb068AlphaDummy319), (nb068AlphaDummy320 f)),
          ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
          ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
          ((nb068AlphaDummy317), (nb068AlphaDummy318 f)),
          ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
          ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
          ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy313) from (by
                                unfold nb068AlphaDummy313;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0314) 0))))
                            (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy314 f) from (by
                                unfold nb068AlphaDummy314;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0315 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy311) from (by
                                  unfold nb068AlphaDummy311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0312) 0))))
                              (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy312 f) from
                                (by
                                  unfold nb068AlphaDummy312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0313 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy313) from (by
                                unfold nb068AlphaDummy313;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0314) 0))))
                            (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy314 f) from (by
                                unfold nb068AlphaDummy314;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0315 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy311) from (by
                                  unfold nb068AlphaDummy311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0312) 0))))
                              (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy312 f) from
                                (by
                                  unfold nb068AlphaDummy312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0313 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy315) from (by
                                unfold nb068AlphaDummy315;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0318) 0))))
                            (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy316 f) from (by
                                unfold nb068AlphaDummy316;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0319 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy311) from (by
                                  unfold nb068AlphaDummy311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0316) 0))))
                              (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy312 f) from
                                (by
                                  unfold nb068AlphaDummy312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0317 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy315) from (by
                                unfold nb068AlphaDummy315;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0318) 0))))
                            (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy316 f) from (by
                                unfold nb068AlphaDummy316;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0319 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy311) from (by
                                  unfold nb068AlphaDummy311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0316) 0))))
                              (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy312 f) from
                                (by
                                  unfold nb068AlphaDummy312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0317 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0087`. -/
@[expose]
noncomputable def nb068SplitAlpha0087 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
        ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
        ((nb068AlphaDummy321), (nb068AlphaDummy322 f)),
        ((nb068AlphaDummy319), (nb068AlphaDummy320 f)),
        ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
        ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
        ((nb068AlphaDummy317), (nb068AlphaDummy318 f)),
        ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
        ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
        ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy295))
          (Class.cv (nb068AlphaDummy288))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy296))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy295)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy295)) (synC1c))
              (Class.cv (nb068AlphaDummy295))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy297 f))
          (Class.cv (nb068AlphaDummy290 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy298 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy297 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy297 f)) (synC1c))
              (Class.cv (nb068AlphaDummy297 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy288) ≠ (nb068AlphaDummy295) from (by
              unfold nb068AlphaDummy295;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0298) 0))))
          (show (nb068AlphaDummy290 f) ≠ (nb068AlphaDummy297 f) from (by
              unfold nb068AlphaDummy297;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0299 f) 0))))
          (TAlphaVar.there (show (nb068AlphaDummy288) ≠ (nb068AlphaDummy296) from (by
                unfold nb068AlphaDummy296;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0298) 1))))
            (show (nb068AlphaDummy290 f) ≠ (nb068AlphaDummy298 f) from (by
                unfold nb068AlphaDummy298;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0299 f) 1))))
            (TAlphaVar.there (show (nb068AlphaDummy288) ≠ (nb068AlphaDummy321) from (by
                  unfold nb068AlphaDummy321;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0328) 0))))
              (show (nb068AlphaDummy290 f) ≠ (nb068AlphaDummy322 f) from (by
                  unfold nb068AlphaDummy322;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0329 f) 0))))
              (TAlphaVar.there (show (nb068AlphaDummy288) ≠ (nb068AlphaDummy319) from (by
                    unfold nb068AlphaDummy319;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0326) 0))))
                (show (nb068AlphaDummy290 f) ≠ (nb068AlphaDummy320 f) from (by
                    unfold nb068AlphaDummy320;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0327 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy288))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068AlphaDummy290 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy295) ≠ (nb068AlphaDummy302) from (by
                                  unfold nb068AlphaDummy302;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0302) 1))))
                              (show (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy305 f) from
                                (by
                                  unfold nb068AlphaDummy305;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0303 f) 1))))
                              (TAlphaVar.there
                                (show (nb068AlphaDummy295) ≠ (nb068AlphaDummy301) from (by
                                    unfold nb068AlphaDummy301;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0302) 0)))) (show
                                  (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy304 f) from (by
                                    unfold nb068AlphaDummy304;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0303 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy295) ≠ (nb068AlphaDummy299) from
                                    (by
                                      unfold nb068AlphaDummy299;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0300)
                                              0)))) (show
                                    (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy300 f) from
                                    (by
                                      unfold nb068AlphaDummy300;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0301 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy303), (nb068AlphaDummy306 f)),
                                  ((nb068AlphaDummy302), (nb068AlphaDummy305 f)),
                                  ((nb068AlphaDummy301), (nb068AlphaDummy304 f)),
                                  ((nb068AlphaDummy299), (nb068AlphaDummy300 f)),
                                  ((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
                                  ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
                                  ((nb068AlphaDummy321), (nb068AlphaDummy322 f)),
                                  ((nb068AlphaDummy319), (nb068AlphaDummy320 f)),
                                  ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
                                  ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
                                  ((nb068AlphaDummy317), (nb068AlphaDummy318 f)),
                                  ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
                                  ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
                                  ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0086 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068AlphaDummy295) ≠ (nb068AlphaDummy299) from (by
                          unfold nb068AlphaDummy299;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                      (show (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy300 f) from (by
                          unfold nb068AlphaDummy300;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy299), (nb068AlphaDummy300 f)),
                      ((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
                      ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
                      ((nb068AlphaDummy321), (nb068AlphaDummy322 f)),
                      ((nb068AlphaDummy319), (nb068AlphaDummy320 f)),
                      ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
                      ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
                      ((nb068AlphaDummy317), (nb068AlphaDummy318 f)),
                      ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
                      ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
                      ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy295) ≠ (nb068AlphaDummy299) from
                      (by
                        unfold nb068AlphaDummy299;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                    (show (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy300 f) from (by
                        unfold nb068AlphaDummy300;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy295) ≠ (nb068AlphaDummy299) from (by
                          unfold nb068AlphaDummy299;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                      (show (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy300 f) from (by
                          unfold nb068AlphaDummy300;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy299), (nb068AlphaDummy300 f)),
                      ((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
                      ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
                      ((nb068AlphaDummy321), (nb068AlphaDummy322 f)),
                      ((nb068AlphaDummy319), (nb068AlphaDummy320 f)),
                      ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
                      ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
                      ((nb068AlphaDummy317), (nb068AlphaDummy318 f)),
                      ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
                      ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
                      ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0088`. -/
@[expose]
noncomputable def nb068SplitAlpha0088 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy317), (nb068AlphaDummy318 f)),
        ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
        ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
        ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy317))
          (Class.cab (nb068AlphaDummy287)
            (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy283))
              (Wff.classEq (Class.cv (nb068AlphaDummy287))
                (synCun (synCphi (Class.cv (nb068AlphaDummy288))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy317))
            (Class.cab (nb068AlphaDummy287)
              (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy283))
                (Wff.classEq (Class.cv (nb068AlphaDummy287))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy288)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy318 f))
          (Class.cab (nb068AlphaDummy289 f)
            (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy285 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy290 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy318 f))
            (Class.cab (nb068AlphaDummy289 f)
              (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy285 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy290 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy283) ≠ (nb068AlphaDummy288) from
                    (by
                      unfold nb068AlphaDummy288;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 1))))
                  (show (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy290 f) from (by
                      unfold nb068AlphaDummy290;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0322 f) 1))))
                  (TAlphaVar.there (show (nb068AlphaDummy283) ≠ (nb068AlphaDummy287) from
                      (by
                        unfold nb068AlphaDummy287;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 0))))
                    (show (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy289 f) from (by
                        unfold nb068AlphaDummy289;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0322 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy283) ≠ (nb068AlphaDummy317) from (by
                          unfold nb068AlphaDummy317;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0324) 0))))
                      (show (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy318 f) from (by
                          unfold nb068AlphaDummy318;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0325 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy283) ≠ (nb068AlphaDummy291) from (by
                            unfold nb068AlphaDummy291;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0321) 0))))
                        (show (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy292 f) from (by
                            unfold nb068AlphaDummy292;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0323 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb068AlphaDummy000))).fv ∪ ((synCvv)).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((synCvv)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy284))).fv ∪
                      ((Class.cv (nb068AlphaDummy283))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068AlphaDummy286 f))).fv ∪
                      ((Class.cv (nb068AlphaDummy285 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0087 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0087 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy319), (nb068AlphaDummy320 f)),
                          ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
                          ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
                          ((nb068AlphaDummy317), (nb068AlphaDummy318 f)),
                          ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
                          ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
                          ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy283) ≠ (nb068AlphaDummy288) from
                      (by
                        unfold nb068AlphaDummy288;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 1))))
                    (show (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy290 f) from (by
                        unfold nb068AlphaDummy290;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0322 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy283) ≠ (nb068AlphaDummy287) from (by
                          unfold nb068AlphaDummy287;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0320) 0))))
                      (show (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy289 f) from (by
                          unfold nb068AlphaDummy289;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0322 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy283) ≠ (nb068AlphaDummy317) from (by
                            unfold nb068AlphaDummy317;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0324) 0))))
                        (show (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy318 f) from (by
                            unfold nb068AlphaDummy318;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0325 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy283) ≠ (nb068AlphaDummy291) from (by
                              unfold nb068AlphaDummy291;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0321) 0))))
                          (show (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy292 f) from (by
                              unfold nb068AlphaDummy292;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0323 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb068AlphaDummy000))).fv ∪ ((synCvv)).fv)
                              (by decide))
                            (freshVar_injective (((Class.cv f)).fv ∪ ((synCvv)).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068AlphaDummy284))).fv ∪
                        ((Class.cv (nb068AlphaDummy283))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy286 f))).fv ∪
                        ((Class.cv (nb068AlphaDummy285 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0087 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0087 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy319), (nb068AlphaDummy320 f)),
                            ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
                            ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
                            ((nb068AlphaDummy317), (nb068AlphaDummy318 f)),
                            ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
                            ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
                            ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
                            ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                            ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

theorem nb068_compact_fv_empty_0272 : (nb068AlphaDummy325) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0273 (f : Var) :
    (nb068AlphaDummy326 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0274 : (nb068AlphaDummy323) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0275 (f : Var) :
    (nb068AlphaDummy324 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
