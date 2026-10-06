/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C095M3Part019Stage1


/-! NF weak partition development: NAR4H5C095M3Part019. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0030`. -/
@[expose]
noncomputable def nb095SplitAlpha0030 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy305 D R S_cls E), (nb095AlphaDummy306 f)),
        ((nb095AlphaDummy303 D R S_cls E), (nb095AlphaDummy304 f)),
        ((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
        ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy305 D R S_cls E))
          (Class.cab (nb095AlphaDummy299 D R S_cls E)
            (synWrex (nb095AlphaDummy300 D R S_cls E)
              (Class.cv (nb095AlphaDummy296 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy305 D R S_cls E))
            (Class.cab (nb095AlphaDummy299 D R S_cls E)
              (synWrex (nb095AlphaDummy300 D R S_cls E)
                (Class.cv (nb095AlphaDummy296 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy306 f))
          (Class.cab (nb095AlphaDummy301 f)
            (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy298 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
                (synCphi (Class.cv (nb095AlphaDummy302 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy306 f))
            (Class.cab (nb095AlphaDummy301 f)
              (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy298 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
                  (synCphi (Class.cv (nb095AlphaDummy302 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy296 D R S_cls E) ≠
                      (nb095AlphaDummy300 D R S_cls E) from (by
                      unfold nb095AlphaDummy300;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0296 D R S_cls E) 1))))
                  (show (nb095AlphaDummy298 f) ≠ (nb095AlphaDummy302 f) from (by
                      unfold nb095AlphaDummy302;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0298 f) 1))))
                  (TAlphaVar.there (show (nb095AlphaDummy296 D R S_cls E) ≠
                        (nb095AlphaDummy299 D R S_cls E) from (by
                        unfold nb095AlphaDummy299;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0296 D R S_cls E) 0))))
                    (show (nb095AlphaDummy298 f) ≠ (nb095AlphaDummy301 f) from (by
                        unfold nb095AlphaDummy301;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0298 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy296 D R S_cls E) ≠
                          (nb095AlphaDummy305 D R S_cls E) from (by
                          unfold nb095AlphaDummy305;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0300 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy298 f) ≠ (nb095AlphaDummy306 f) from (by
                          unfold nb095AlphaDummy306;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0301 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy296 D R S_cls E) ≠
                            (nb095AlphaDummy303 D R S_cls E) from (by
                            unfold nb095AlphaDummy303;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0297 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy298 f) ≠ (nb095AlphaDummy304 f) from (by
                            unfold nb095AlphaDummy304;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0299 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy296 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy295 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy298 f))).fv ∪
                      ((Class.cv (nb095AlphaDummy297 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy300 D R S_cls E) ≠
                              (nb095AlphaDummy307 D R S_cls E) from (by
                              unfold nb095AlphaDummy307;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0302 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy309 f) from (by
                              unfold nb095AlphaDummy309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0303 f) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy300 D R S_cls E) ≠
                                (nb095AlphaDummy308 D R S_cls E) from (by
                                unfold nb095AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0302 D R S_cls E) 1))))
                            (show (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy310 f) from (by
                                unfold nb095AlphaDummy310;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0303 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy300 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy302 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy314 D R S_cls E) from (by
          unfold nb095AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy317 f) from (by
          unfold nb095AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy307 D R S_cls E) ≠ (nb095AlphaDummy313 D R S_cls E) from (by
          unfold nb095AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy316 f) from (by
          unfold nb095AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy307 D R S_cls E) ≠ (nb095AlphaDummy311 D R S_cls E) from (by
          unfold nb095AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0304 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from (by
          unfold nb095AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0305 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy315 D R S_cls E), (nb095AlphaDummy318 f)),
        ((nb095AlphaDummy314 D R S_cls E), (nb095AlphaDummy317 f)),
        ((nb095AlphaDummy313 D R S_cls E), (nb095AlphaDummy316 f)),
        ((nb095AlphaDummy311 D R S_cls E), (nb095AlphaDummy312 f)),
        ((nb095AlphaDummy307 D R S_cls E), (nb095AlphaDummy309 f)),
        ((nb095AlphaDummy308 D R S_cls E), (nb095AlphaDummy310 f)),
        ((nb095AlphaDummy300 D R S_cls E), (nb095AlphaDummy302 f)),
        ((nb095AlphaDummy299 D R S_cls E), (nb095AlphaDummy301 f)),
        ((nb095AlphaDummy305 D R S_cls E), (nb095AlphaDummy306 f)),
        ((nb095AlphaDummy303 D R S_cls E), (nb095AlphaDummy304 f)),
        ((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
        ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy314
        D R S_cls E) ≠ (nb095AlphaDummy321 D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy322 f) from (by
          unfold
            nb095AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0311
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠
        (nb095AlphaDummy319 D R S_cls E) from (by
          unfold
            nb095AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0308
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy320 f) from (by
          unfold
            nb095AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0309
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠ (nb095AlphaDummy321
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy322 f) from (by
          unfold
            nb095AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0315
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠
        (nb095AlphaDummy319 D R S_cls E) from (by
          unfold
            nb095AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0312
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy320 f) from (by
          unfold
            nb095AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0313
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠ (nb095AlphaDummy321
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy322 f) from (by
          unfold
            nb095AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0311
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠
        (nb095AlphaDummy319 D R S_cls E) from (by
          unfold
            nb095AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0308
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy320 f) from (by
          unfold
            nb095AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0309
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠ (nb095AlphaDummy321
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy322 f) from (by
          unfold
            nb095AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0315
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠
        (nb095AlphaDummy319 D R S_cls E) from (by
          unfold
            nb095AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0312
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy320 f) from (by
          unfold
            nb095AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0313
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy315 D R S_cls E), (nb095AlphaDummy318 f)),
        ((nb095AlphaDummy314 D R S_cls E), (nb095AlphaDummy317 f)),
        ((nb095AlphaDummy313 D R S_cls E), (nb095AlphaDummy316 f)),
        ((nb095AlphaDummy311 D R S_cls E), (nb095AlphaDummy312 f)),
        ((nb095AlphaDummy307 D R S_cls E), (nb095AlphaDummy309 f)),
        ((nb095AlphaDummy308 D R S_cls E), (nb095AlphaDummy310 f)),
        ((nb095AlphaDummy300 D R S_cls E), (nb095AlphaDummy302 f)),
        ((nb095AlphaDummy299 D R S_cls E), (nb095AlphaDummy301 f)),
        ((nb095AlphaDummy305 D R S_cls E), (nb095AlphaDummy306 f)),
        ((nb095AlphaDummy303 D R S_cls E), (nb095AlphaDummy304 f)),
        ((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
        ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy307 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠ (nb095AlphaDummy325
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy326 f) from (by
          unfold
            nb095AlphaDummy326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0319
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠
        (nb095AlphaDummy323 D R S_cls E) from (by
          unfold
            nb095AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0316
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy324 f) from (by
          unfold
            nb095AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0317
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠ (nb095AlphaDummy325
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy326 f) from (by
          unfold
            nb095AlphaDummy326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0319
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠
        (nb095AlphaDummy323 D R S_cls E) from (by
          unfold
            nb095AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0316
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy324 f) from (by
          unfold
            nb095AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0317
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy315
        D R S_cls E) ≠ (nb095AlphaDummy327 D R S_cls E) from (by
          unfold
            nb095AlphaDummy327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0322
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy328 f) from (by
          unfold
            nb095AlphaDummy328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0323
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠
        (nb095AlphaDummy323 D R S_cls E) from (by
          unfold
            nb095AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0320
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy324 f) from (by
          unfold
            nb095AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0321
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy315
        D R S_cls E) ≠ (nb095AlphaDummy327 D R S_cls E) from (by
          unfold
            nb095AlphaDummy327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0322
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy328 f) from (by
          unfold
            nb095AlphaDummy328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0323
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠
        (nb095AlphaDummy323 D R S_cls E) from (by
          unfold
            nb095AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0320
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy324 f) from (by
          unfold
            nb095AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0321
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy307 D R S_cls E) ≠
                                        (nb095AlphaDummy311 D R S_cls E) from (by
                                        unfold nb095AlphaDummy311;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0304 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from
                                      (by
                                        unfold nb095AlphaDummy312;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0305 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy311 D R S_cls E),
                                      (nb095AlphaDummy312 f)),
                                    ((nb095AlphaDummy307 D R S_cls E),
                                      (nb095AlphaDummy309 f)),
                                    ((nb095AlphaDummy308 D R S_cls E),
                                      (nb095AlphaDummy310 f)),
                                    ((nb095AlphaDummy300 D R S_cls E),
                                      (nb095AlphaDummy302 f)),
                                    ((nb095AlphaDummy299 D R S_cls E),
                                      (nb095AlphaDummy301 f)),
                                    ((nb095AlphaDummy305 D R S_cls E),
                                      (nb095AlphaDummy306 f)),
                                    ((nb095AlphaDummy303 D R S_cls E),
                                      (nb095AlphaDummy304 f)),
                                    ((nb095AlphaDummy296 D R S_cls E),
                                      (nb095AlphaDummy298 f)),
                                    ((nb095AlphaDummy295 D R S_cls E),
                                      (nb095AlphaDummy297 f)),
                                    ((nb095AlphaDummy293 D R S_cls E),
                                      (nb095AlphaDummy294 u S_cls f E)),
                                    ((nb095AlphaDummy291 D R S_cls E),
                                      (nb095AlphaDummy292 u S_cls f E)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy307 D R S_cls E) ≠
                                      (nb095AlphaDummy311 D R S_cls E) from (by
                                      unfold nb095AlphaDummy311;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0304 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from
                                    (by
                                      unfold nb095AlphaDummy312;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0305 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy307 D R S_cls E) ≠
                                        (nb095AlphaDummy311 D R S_cls E) from (by
                                        unfold nb095AlphaDummy311;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0304 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from
                                      (by
                                        unfold nb095AlphaDummy312;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0305 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy311 D R S_cls E),
                                      (nb095AlphaDummy312 f)),
                                    ((nb095AlphaDummy307 D R S_cls E),
                                      (nb095AlphaDummy309 f)),
                                    ((nb095AlphaDummy308 D R S_cls E),
                                      (nb095AlphaDummy310 f)),
                                    ((nb095AlphaDummy300 D R S_cls E),
                                      (nb095AlphaDummy302 f)),
                                    ((nb095AlphaDummy299 D R S_cls E),
                                      (nb095AlphaDummy301 f)),
                                    ((nb095AlphaDummy305 D R S_cls E),
                                      (nb095AlphaDummy306 f)),
                                    ((nb095AlphaDummy303 D R S_cls E),
                                      (nb095AlphaDummy304 f)),
                                    ((nb095AlphaDummy296 D R S_cls E),
                                      (nb095AlphaDummy298 f)),
                                    ((nb095AlphaDummy295 D R S_cls E),
                                      (nb095AlphaDummy297 f)),
                                    ((nb095AlphaDummy293 D R S_cls E),
                                      (nb095AlphaDummy294 u S_cls f E)),
                                    ((nb095AlphaDummy291 D R S_cls E),
                                      (nb095AlphaDummy292 u S_cls f E)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095AlphaDummy296 D R S_cls E) ≠
                        (nb095AlphaDummy300 D R S_cls E) from (by
                        unfold nb095AlphaDummy300;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0296 D R S_cls E) 1))))
                    (show (nb095AlphaDummy298 f) ≠ (nb095AlphaDummy302 f) from (by
                        unfold nb095AlphaDummy302;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0298 f) 1)))) (TAlphaVar.there
                      (show (nb095AlphaDummy296 D R S_cls E) ≠
                          (nb095AlphaDummy299 D R S_cls E) from (by
                          unfold nb095AlphaDummy299;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0296 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy298 f) ≠ (nb095AlphaDummy301 f) from (by
                          unfold nb095AlphaDummy301;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0298 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy296 D R S_cls E) ≠
                            (nb095AlphaDummy305 D R S_cls E) from (by
                            unfold nb095AlphaDummy305;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0300 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy298 f) ≠ (nb095AlphaDummy306 f) from (by
                            unfold nb095AlphaDummy306;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0301 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy296 D R S_cls E) ≠
                              (nb095AlphaDummy303 D R S_cls E) from (by
                              unfold nb095AlphaDummy303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0297 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy298 f) ≠ (nb095AlphaDummy304 f) from (by
                              unfold nb095AlphaDummy304;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0299 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy296 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy295 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy298 f))).fv ∪
                        ((Class.cv (nb095AlphaDummy297 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy300 D R S_cls E) ≠
                                (nb095AlphaDummy307 D R S_cls E) from (by
                                unfold nb095AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0302 D R S_cls E) 0))))
                            (show (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy309 f) from (by
                                unfold nb095AlphaDummy309;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0303 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy300 D R S_cls E) ≠
                                  (nb095AlphaDummy308 D R S_cls E) from (by
                                  unfold nb095AlphaDummy308;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0302 D R S_cls E) 1))))
                              (show (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy310 f) from
                                (by
                                  unfold nb095AlphaDummy310;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0303 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy300 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy302 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy307 D R S_cls E) ≠ (nb095AlphaDummy314 D R S_cls E) from (by
          unfold nb095AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy317 f) from (by
          unfold nb095AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy307 D R S_cls E) ≠ (nb095AlphaDummy313 D R S_cls E) from (by
          unfold nb095AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy316 f) from (by
          unfold nb095AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy311 D R S_cls E) from (by
          unfold nb095AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0304 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from (by
          unfold nb095AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0305 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy315 D R S_cls E), (nb095AlphaDummy318 f)),
        ((nb095AlphaDummy314 D R S_cls E), (nb095AlphaDummy317 f)),
        ((nb095AlphaDummy313 D R S_cls E), (nb095AlphaDummy316 f)),
        ((nb095AlphaDummy311 D R S_cls E), (nb095AlphaDummy312 f)),
        ((nb095AlphaDummy307 D R S_cls E), (nb095AlphaDummy309 f)),
        ((nb095AlphaDummy308 D R S_cls E), (nb095AlphaDummy310 f)),
        ((nb095AlphaDummy300 D R S_cls E), (nb095AlphaDummy302 f)),
        ((nb095AlphaDummy299 D R S_cls E), (nb095AlphaDummy301 f)),
        ((nb095AlphaDummy305 D R S_cls E), (nb095AlphaDummy306 f)),
        ((nb095AlphaDummy303 D R S_cls E), (nb095AlphaDummy304 f)),
        ((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
        ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy314
        D R S_cls E) ≠ (nb095AlphaDummy321 D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy322 f) from (by
          unfold
            nb095AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0311
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠
        (nb095AlphaDummy319 D R S_cls E) from (by
          unfold
            nb095AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0308
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy320 f) from (by
          unfold
            nb095AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0309
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠ (nb095AlphaDummy321
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy322 f) from (by
          unfold
            nb095AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0315
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠
        (nb095AlphaDummy319 D R S_cls E) from (by
          unfold
            nb095AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0312
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy320 f) from (by
          unfold
            nb095AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0313
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠ (nb095AlphaDummy321
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy322 f) from (by
          unfold
            nb095AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0311
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠
        (nb095AlphaDummy319 D R S_cls E) from (by
          unfold
            nb095AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0308
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy320 f) from (by
          unfold
            nb095AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0309
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠ (nb095AlphaDummy321
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy322 f) from (by
          unfold
            nb095AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0315
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠
        (nb095AlphaDummy319 D R S_cls E) from (by
          unfold
            nb095AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0312
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy320 f) from (by
          unfold
            nb095AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0313
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy315 D R S_cls E), (nb095AlphaDummy318 f)),
        ((nb095AlphaDummy314 D R S_cls E), (nb095AlphaDummy317 f)),
        ((nb095AlphaDummy313 D R S_cls E), (nb095AlphaDummy316 f)),
        ((nb095AlphaDummy311 D R S_cls E), (nb095AlphaDummy312 f)),
        ((nb095AlphaDummy307 D R S_cls E), (nb095AlphaDummy309 f)),
        ((nb095AlphaDummy308 D R S_cls E), (nb095AlphaDummy310 f)),
        ((nb095AlphaDummy300 D R S_cls E), (nb095AlphaDummy302 f)),
        ((nb095AlphaDummy299 D R S_cls E), (nb095AlphaDummy301 f)),
        ((nb095AlphaDummy305 D R S_cls E), (nb095AlphaDummy306 f)),
        ((nb095AlphaDummy303 D R S_cls E), (nb095AlphaDummy304 f)),
        ((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
        ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy307 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠ (nb095AlphaDummy325
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy326 f) from (by
          unfold
            nb095AlphaDummy326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0319
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠
        (nb095AlphaDummy323 D R S_cls E) from (by
          unfold
            nb095AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0316
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy324 f) from (by
          unfold
            nb095AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0317
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠ (nb095AlphaDummy325
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy326 f) from (by
          unfold
            nb095AlphaDummy326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0319
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠
        (nb095AlphaDummy323 D R S_cls E) from (by
          unfold
            nb095AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0316
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy324 f) from (by
          unfold
            nb095AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0317
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy315
        D R S_cls E) ≠ (nb095AlphaDummy327 D R S_cls E) from (by
          unfold
            nb095AlphaDummy327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0322
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy328 f) from (by
          unfold
            nb095AlphaDummy328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0323
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠
        (nb095AlphaDummy323 D R S_cls E) from (by
          unfold
            nb095AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0320
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy324 f) from (by
          unfold
            nb095AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0321
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy315
        D R S_cls E) ≠ (nb095AlphaDummy327 D R S_cls E) from (by
          unfold
            nb095AlphaDummy327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0322
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy328 f) from (by
          unfold
            nb095AlphaDummy328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0323
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠
        (nb095AlphaDummy323 D R S_cls E) from (by
          unfold
            nb095AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0320
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy324 f) from (by
          unfold
            nb095AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0321
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy311 D R S_cls E) from (by
                                          unfold nb095AlphaDummy311;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0304 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy309 f) ≠
        (nb095AlphaDummy312 f) from (by
                                          unfold nb095AlphaDummy312;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0305 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy311 D R S_cls E),
                                        (nb095AlphaDummy312 f)),
                                      ((nb095AlphaDummy307 D R S_cls E),
                                        (nb095AlphaDummy309 f)),
                                      ((nb095AlphaDummy308 D R S_cls E),
                                        (nb095AlphaDummy310 f)),
                                      ((nb095AlphaDummy300 D R S_cls E),
                                        (nb095AlphaDummy302 f)),
                                      ((nb095AlphaDummy299 D R S_cls E),
                                        (nb095AlphaDummy301 f)),
                                      ((nb095AlphaDummy305 D R S_cls E),
                                        (nb095AlphaDummy306 f)),
                                      ((nb095AlphaDummy303 D R S_cls E),
                                        (nb095AlphaDummy304 f)),
                                      ((nb095AlphaDummy296 D R S_cls E),
                                        (nb095AlphaDummy298 f)),
                                      ((nb095AlphaDummy295 D R S_cls E),
                                        (nb095AlphaDummy297 f)),
                                      ((nb095AlphaDummy293 D R S_cls E),
                                        (nb095AlphaDummy294 u S_cls f E)),
                                      ((nb095AlphaDummy291 D R S_cls E),
                                        (nb095AlphaDummy292 u S_cls f E)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy307 D R S_cls E) ≠
                                        (nb095AlphaDummy311 D R S_cls E) from (by
                                        unfold nb095AlphaDummy311;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0304 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from
                                      (by
                                        unfold nb095AlphaDummy312;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0305 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy311 D R S_cls E) from (by
                                          unfold nb095AlphaDummy311;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0304 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy309 f) ≠
        (nb095AlphaDummy312 f) from (by
                                          unfold nb095AlphaDummy312;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0305 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy311 D R S_cls E),
                                        (nb095AlphaDummy312 f)),
                                      ((nb095AlphaDummy307 D R S_cls E),
                                        (nb095AlphaDummy309 f)),
                                      ((nb095AlphaDummy308 D R S_cls E),
                                        (nb095AlphaDummy310 f)),
                                      ((nb095AlphaDummy300 D R S_cls E),
                                        (nb095AlphaDummy302 f)),
                                      ((nb095AlphaDummy299 D R S_cls E),
                                        (nb095AlphaDummy301 f)),
                                      ((nb095AlphaDummy305 D R S_cls E),
                                        (nb095AlphaDummy306 f)),
                                      ((nb095AlphaDummy303 D R S_cls E),
                                        (nb095AlphaDummy304 f)),
                                      ((nb095AlphaDummy296 D R S_cls E),
                                        (nb095AlphaDummy298 f)),
                                      ((nb095AlphaDummy295 D R S_cls E),
                                        (nb095AlphaDummy297 f)),
                                      ((nb095AlphaDummy293 D R S_cls E),
                                        (nb095AlphaDummy294 u S_cls f E)),
                                      ((nb095AlphaDummy291 D R S_cls E),
                                        (nb095AlphaDummy292 u S_cls f E)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0031`. -/
@[expose]
noncomputable def nb095SplitAlpha0031 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy331 D R S_cls E), (nb095AlphaDummy332 f)),
        ((nb095AlphaDummy300 D R S_cls E), (nb095AlphaDummy302 f)),
        ((nb095AlphaDummy299 D R S_cls E), (nb095AlphaDummy301 f)),
        ((nb095AlphaDummy329 D R S_cls E), (nb095AlphaDummy330 f)),
        ((nb095AlphaDummy303 D R S_cls E), (nb095AlphaDummy304 f)),
        ((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
        ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb095AlphaDummy331 D R S_cls E))
            (synCcompl (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))))
          (Wff.classMem (Class.cv (nb095AlphaDummy331 D R S_cls E))
            (synCcompl (synCsn (synC0c))))))
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb095AlphaDummy332 f))
            (synCcompl (synCphi (Class.cv (nb095AlphaDummy302 f)))))
          (Wff.classMem (Class.cv (nb095AlphaDummy332 f))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy300 D R S_cls E) ≠
                                (nb095AlphaDummy307 D R S_cls E) from (by
                                unfold nb095AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0302 D R S_cls E) 0))))
                            (show (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy309 f) from (by
                                unfold nb095AlphaDummy309;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0303 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy300 D R S_cls E) ≠
                                  (nb095AlphaDummy308 D R S_cls E) from (by
                                  unfold nb095AlphaDummy308;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0302 D R S_cls E) 1))))
                              (show (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy310 f) from
                                (by
                                  unfold nb095AlphaDummy310;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0303 f) 1))))
                              (TAlphaVar.there (show (nb095AlphaDummy300 D R S_cls E) ≠
                                    (nb095AlphaDummy333 D R S_cls E) from (by
                                    unfold nb095AlphaDummy333;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0332 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy334 f) from (by
                                    unfold nb095AlphaDummy334;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0333 f)
                                            0)))) (TAlphaVar.there (show
                                    (nb095AlphaDummy300 D R S_cls E) ≠
                                      (nb095AlphaDummy331 D R S_cls E) from (by
                                      unfold nb095AlphaDummy331;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0330 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy332 f) from
                                    (by
                                      unfold nb095AlphaDummy332;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0331 f)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy300 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy302 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy307 D R S_cls E) ≠ (nb095AlphaDummy314 D R S_cls E) from (by
          unfold nb095AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy317 f) from (by
          unfold nb095AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy307 D R S_cls E) ≠ (nb095AlphaDummy313 D R S_cls E) from (by
          unfold nb095AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy316 f) from (by
          unfold nb095AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy311 D R S_cls E) from (by
          unfold nb095AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0304 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from (by
          unfold nb095AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0305 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy315 D R S_cls E), (nb095AlphaDummy318 f)),
        ((nb095AlphaDummy314 D R S_cls E), (nb095AlphaDummy317 f)),
        ((nb095AlphaDummy313 D R S_cls E), (nb095AlphaDummy316 f)),
        ((nb095AlphaDummy311 D R S_cls E), (nb095AlphaDummy312 f)),
        ((nb095AlphaDummy307 D R S_cls E), (nb095AlphaDummy309 f)),
        ((nb095AlphaDummy308 D R S_cls E), (nb095AlphaDummy310 f)),
        ((nb095AlphaDummy333 D R S_cls E), (nb095AlphaDummy334 f)),
        ((nb095AlphaDummy331 D R S_cls E), (nb095AlphaDummy332 f)),
        ((nb095AlphaDummy300 D R S_cls E), (nb095AlphaDummy302 f)),
        ((nb095AlphaDummy299 D R S_cls E), (nb095AlphaDummy301 f)),
        ((nb095AlphaDummy329 D R S_cls E), (nb095AlphaDummy330 f)),
        ((nb095AlphaDummy303 D R S_cls E), (nb095AlphaDummy304 f)),
        ((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
        ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy314
        D R S_cls E) ≠ (nb095AlphaDummy321 D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy322 f) from (by
          unfold
            nb095AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0311
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠
        (nb095AlphaDummy319 D R S_cls E) from (by
          unfold
            nb095AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0308
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy320 f) from (by
          unfold
            nb095AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0309
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠ (nb095AlphaDummy321
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy322 f) from (by
          unfold
            nb095AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0315
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠
        (nb095AlphaDummy319 D R S_cls E) from (by
          unfold
            nb095AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0312
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy320 f) from (by
          unfold
            nb095AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0313
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠ (nb095AlphaDummy321
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy322 f) from (by
          unfold
            nb095AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0311
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠
        (nb095AlphaDummy319 D R S_cls E) from (by
          unfold
            nb095AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0308
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy320 f) from (by
          unfold
            nb095AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0309
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠ (nb095AlphaDummy321
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy322 f) from (by
          unfold
            nb095AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0315
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠
        (nb095AlphaDummy319 D R S_cls E) from (by
          unfold
            nb095AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0312
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy320 f) from (by
          unfold
            nb095AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0313
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy315 D R S_cls E), (nb095AlphaDummy318 f)),
        ((nb095AlphaDummy314 D R S_cls E), (nb095AlphaDummy317 f)),
        ((nb095AlphaDummy313 D R S_cls E), (nb095AlphaDummy316 f)),
        ((nb095AlphaDummy311 D R S_cls E), (nb095AlphaDummy312 f)),
        ((nb095AlphaDummy307 D R S_cls E), (nb095AlphaDummy309 f)),
        ((nb095AlphaDummy308 D R S_cls E), (nb095AlphaDummy310 f)),
        ((nb095AlphaDummy333 D R S_cls E), (nb095AlphaDummy334 f)),
        ((nb095AlphaDummy331 D R S_cls E), (nb095AlphaDummy332 f)),
        ((nb095AlphaDummy300 D R S_cls E), (nb095AlphaDummy302 f)),
        ((nb095AlphaDummy299 D R S_cls E), (nb095AlphaDummy301 f)),
        ((nb095AlphaDummy329 D R S_cls E), (nb095AlphaDummy330 f)),
        ((nb095AlphaDummy303 D R S_cls E), (nb095AlphaDummy304 f)),
        ((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
        ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy307 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠ (nb095AlphaDummy325
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy326 f) from (by
          unfold
            nb095AlphaDummy326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0319
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠
        (nb095AlphaDummy323 D R S_cls E) from (by
          unfold
            nb095AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0316
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy324 f) from (by
          unfold
            nb095AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0317
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠ (nb095AlphaDummy325
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy326 f) from (by
          unfold
            nb095AlphaDummy326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0319
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠
        (nb095AlphaDummy323 D R S_cls E) from (by
          unfold
            nb095AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0316
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy324 f) from (by
          unfold
            nb095AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0317
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy315
        D R S_cls E) ≠ (nb095AlphaDummy327 D R S_cls E) from (by
          unfold
            nb095AlphaDummy327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0322
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy328 f) from (by
          unfold
            nb095AlphaDummy328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0323
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠
        (nb095AlphaDummy323 D R S_cls E) from (by
          unfold
            nb095AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0320
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy324 f) from (by
          unfold
            nb095AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0321
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy315
        D R S_cls E) ≠ (nb095AlphaDummy327 D R S_cls E) from (by
          unfold
            nb095AlphaDummy327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0322
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy328 f) from (by
          unfold
            nb095AlphaDummy328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0323
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠
        (nb095AlphaDummy323 D R S_cls E) from (by
          unfold
            nb095AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0320
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy324 f) from (by
          unfold
            nb095AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0321
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy311 D R S_cls E) from (by
                                          unfold nb095AlphaDummy311;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0304 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy309 f) ≠
        (nb095AlphaDummy312 f) from (by
                                          unfold nb095AlphaDummy312;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0305 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy311 D R S_cls E),
                                        (nb095AlphaDummy312 f)),
                                      ((nb095AlphaDummy307 D R S_cls E),
                                        (nb095AlphaDummy309 f)),
                                      ((nb095AlphaDummy308 D R S_cls E),
                                        (nb095AlphaDummy310 f)),
                                      ((nb095AlphaDummy333 D R S_cls E),
                                        (nb095AlphaDummy334 f)),
                                      ((nb095AlphaDummy331 D R S_cls E),
                                        (nb095AlphaDummy332 f)),
                                      ((nb095AlphaDummy300 D R S_cls E),
                                        (nb095AlphaDummy302 f)),
                                      ((nb095AlphaDummy299 D R S_cls E),
                                        (nb095AlphaDummy301 f)),
                                      ((nb095AlphaDummy329 D R S_cls E),
                                        (nb095AlphaDummy330 f)),
                                      ((nb095AlphaDummy303 D R S_cls E),
                                        (nb095AlphaDummy304 f)),
                                      ((nb095AlphaDummy296 D R S_cls E),
                                        (nb095AlphaDummy298 f)),
                                      ((nb095AlphaDummy295 D R S_cls E),
                                        (nb095AlphaDummy297 f)),
                                      ((nb095AlphaDummy293 D R S_cls E),
                                        (nb095AlphaDummy294 u S_cls f E)),
                                      ((nb095AlphaDummy291 D R S_cls E),
                                        (nb095AlphaDummy292 u S_cls f E)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy307 D R S_cls E) ≠
                                        (nb095AlphaDummy311 D R S_cls E) from (by
                                        unfold nb095AlphaDummy311;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0304 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from
                                      (by
                                        unfold nb095AlphaDummy312;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0305 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy311 D R S_cls E) from (by
                                          unfold nb095AlphaDummy311;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0304 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy309 f) ≠
        (nb095AlphaDummy312 f) from (by
                                          unfold nb095AlphaDummy312;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0305 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy311 D R S_cls E),
                                        (nb095AlphaDummy312 f)),
                                      ((nb095AlphaDummy307 D R S_cls E),
                                        (nb095AlphaDummy309 f)),
                                      ((nb095AlphaDummy308 D R S_cls E),
                                        (nb095AlphaDummy310 f)),
                                      ((nb095AlphaDummy333 D R S_cls E),
                                        (nb095AlphaDummy334 f)),
                                      ((nb095AlphaDummy331 D R S_cls E),
                                        (nb095AlphaDummy332 f)),
                                      ((nb095AlphaDummy300 D R S_cls E),
                                        (nb095AlphaDummy302 f)),
                                      ((nb095AlphaDummy299 D R S_cls E),
                                        (nb095AlphaDummy301 f)),
                                      ((nb095AlphaDummy329 D R S_cls E),
                                        (nb095AlphaDummy330 f)),
                                      ((nb095AlphaDummy303 D R S_cls E),
                                        (nb095AlphaDummy304 f)),
                                      ((nb095AlphaDummy296 D R S_cls E),
                                        (nb095AlphaDummy298 f)),
                                      ((nb095AlphaDummy295 D R S_cls E),
                                        (nb095AlphaDummy297 f)),
                                      ((nb095AlphaDummy293 D R S_cls E),
                                        (nb095AlphaDummy294 u S_cls f E)),
                                      ((nb095AlphaDummy291 D R S_cls E),
                                        (nb095AlphaDummy292 u S_cls f E)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy300 D R S_cls E) ≠
                                (nb095AlphaDummy307 D R S_cls E) from (by
                                unfold nb095AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0302 D R S_cls E) 0))))
                            (show (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy309 f) from (by
                                unfold nb095AlphaDummy309;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0303 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy300 D R S_cls E) ≠
                                  (nb095AlphaDummy308 D R S_cls E) from (by
                                  unfold nb095AlphaDummy308;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0302 D R S_cls E) 1))))
                              (show (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy310 f) from
                                (by
                                  unfold nb095AlphaDummy310;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0303 f) 1))))
                              (TAlphaVar.there (show (nb095AlphaDummy300 D R S_cls E) ≠
                                    (nb095AlphaDummy333 D R S_cls E) from (by
                                    unfold nb095AlphaDummy333;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0332 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy334 f) from (by
                                    unfold nb095AlphaDummy334;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0333 f)
                                            0)))) (TAlphaVar.there (show
                                    (nb095AlphaDummy300 D R S_cls E) ≠
                                      (nb095AlphaDummy331 D R S_cls E) from (by
                                      unfold nb095AlphaDummy331;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0330 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy332 f) from
                                    (by
                                      unfold nb095AlphaDummy332;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0331 f)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy300 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy302 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy307 D R S_cls E) ≠ (nb095AlphaDummy314 D R S_cls E) from (by
          unfold nb095AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy317 f) from (by
          unfold nb095AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy307 D R S_cls E) ≠ (nb095AlphaDummy313 D R S_cls E) from (by
          unfold nb095AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy316 f) from (by
          unfold nb095AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy311 D R S_cls E) from (by
          unfold nb095AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0304 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from (by
          unfold nb095AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0305 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy315 D R S_cls E), (nb095AlphaDummy318 f)),
        ((nb095AlphaDummy314 D R S_cls E), (nb095AlphaDummy317 f)),
        ((nb095AlphaDummy313 D R S_cls E), (nb095AlphaDummy316 f)),
        ((nb095AlphaDummy311 D R S_cls E), (nb095AlphaDummy312 f)),
        ((nb095AlphaDummy307 D R S_cls E), (nb095AlphaDummy309 f)),
        ((nb095AlphaDummy308 D R S_cls E), (nb095AlphaDummy310 f)),
        ((nb095AlphaDummy333 D R S_cls E), (nb095AlphaDummy334 f)),
        ((nb095AlphaDummy331 D R S_cls E), (nb095AlphaDummy332 f)),
        ((nb095AlphaDummy300 D R S_cls E), (nb095AlphaDummy302 f)),
        ((nb095AlphaDummy299 D R S_cls E), (nb095AlphaDummy301 f)),
        ((nb095AlphaDummy329 D R S_cls E), (nb095AlphaDummy330 f)),
        ((nb095AlphaDummy303 D R S_cls E), (nb095AlphaDummy304 f)),
        ((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
        ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy314
        D R S_cls E) ≠ (nb095AlphaDummy321 D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy322 f) from (by
          unfold
            nb095AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0311
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠
        (nb095AlphaDummy319 D R S_cls E) from (by
          unfold
            nb095AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0308
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy320 f) from (by
          unfold
            nb095AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0309
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠ (nb095AlphaDummy321
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy322 f) from (by
          unfold
            nb095AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0315
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠
        (nb095AlphaDummy319 D R S_cls E) from (by
          unfold
            nb095AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0312
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy320 f) from (by
          unfold
            nb095AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0313
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠ (nb095AlphaDummy321
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy322 f) from (by
          unfold
            nb095AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0311
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠
        (nb095AlphaDummy319 D R S_cls E) from (by
          unfold
            nb095AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0308
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy320 f) from (by
          unfold
            nb095AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0309
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠ (nb095AlphaDummy321
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy322 f) from (by
          unfold
            nb095AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0315
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠
        (nb095AlphaDummy319 D R S_cls E) from (by
          unfold
            nb095AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0312
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy320 f) from (by
          unfold
            nb095AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0313
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy315 D R S_cls E), (nb095AlphaDummy318 f)),
        ((nb095AlphaDummy314 D R S_cls E), (nb095AlphaDummy317 f)),
        ((nb095AlphaDummy313 D R S_cls E), (nb095AlphaDummy316 f)),
        ((nb095AlphaDummy311 D R S_cls E), (nb095AlphaDummy312 f)),
        ((nb095AlphaDummy307 D R S_cls E), (nb095AlphaDummy309 f)),
        ((nb095AlphaDummy308 D R S_cls E), (nb095AlphaDummy310 f)),
        ((nb095AlphaDummy333 D R S_cls E), (nb095AlphaDummy334 f)),
        ((nb095AlphaDummy331 D R S_cls E), (nb095AlphaDummy332 f)),
        ((nb095AlphaDummy300 D R S_cls E), (nb095AlphaDummy302 f)),
        ((nb095AlphaDummy299 D R S_cls E), (nb095AlphaDummy301 f)),
        ((nb095AlphaDummy329 D R S_cls E), (nb095AlphaDummy330 f)),
        ((nb095AlphaDummy303 D R S_cls E), (nb095AlphaDummy304 f)),
        ((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
        ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy307 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠ (nb095AlphaDummy325
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy326 f) from (by
          unfold
            nb095AlphaDummy326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0319
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠
        (nb095AlphaDummy323 D R S_cls E) from (by
          unfold
            nb095AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0316
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy324 f) from (by
          unfold
            nb095AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0317
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠ (nb095AlphaDummy325
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy326 f) from (by
          unfold
            nb095AlphaDummy326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0319
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠
        (nb095AlphaDummy323 D R S_cls E) from (by
          unfold
            nb095AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0316
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy324 f) from (by
          unfold
            nb095AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0317
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy315
        D R S_cls E) ≠ (nb095AlphaDummy327 D R S_cls E) from (by
          unfold
            nb095AlphaDummy327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0322
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy328 f) from (by
          unfold
            nb095AlphaDummy328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0323
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠
        (nb095AlphaDummy323 D R S_cls E) from (by
          unfold
            nb095AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0320
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy324 f) from (by
          unfold
            nb095AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0321
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy315
        D R S_cls E) ≠ (nb095AlphaDummy327 D R S_cls E) from (by
          unfold
            nb095AlphaDummy327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0322
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy328 f) from (by
          unfold
            nb095AlphaDummy328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0323
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠
        (nb095AlphaDummy323 D R S_cls E) from (by
          unfold
            nb095AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0320
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy318 f) ≠ (nb095AlphaDummy324 f) from (by
          unfold
            nb095AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0321
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy311 D R S_cls E) from (by
                                          unfold nb095AlphaDummy311;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0304 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy309 f) ≠
        (nb095AlphaDummy312 f) from (by
                                          unfold nb095AlphaDummy312;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0305 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy311 D R S_cls E),
                                        (nb095AlphaDummy312 f)),
                                      ((nb095AlphaDummy307 D R S_cls E),
                                        (nb095AlphaDummy309 f)),
                                      ((nb095AlphaDummy308 D R S_cls E),
                                        (nb095AlphaDummy310 f)),
                                      ((nb095AlphaDummy333 D R S_cls E),
                                        (nb095AlphaDummy334 f)),
                                      ((nb095AlphaDummy331 D R S_cls E),
                                        (nb095AlphaDummy332 f)),
                                      ((nb095AlphaDummy300 D R S_cls E),
                                        (nb095AlphaDummy302 f)),
                                      ((nb095AlphaDummy299 D R S_cls E),
                                        (nb095AlphaDummy301 f)),
                                      ((nb095AlphaDummy329 D R S_cls E),
                                        (nb095AlphaDummy330 f)),
                                      ((nb095AlphaDummy303 D R S_cls E),
                                        (nb095AlphaDummy304 f)),
                                      ((nb095AlphaDummy296 D R S_cls E),
                                        (nb095AlphaDummy298 f)),
                                      ((nb095AlphaDummy295 D R S_cls E),
                                        (nb095AlphaDummy297 f)),
                                      ((nb095AlphaDummy293 D R S_cls E),
                                        (nb095AlphaDummy294 u S_cls f E)),
                                      ((nb095AlphaDummy291 D R S_cls E),
                                        (nb095AlphaDummy292 u S_cls f E)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy307 D R S_cls E) ≠
                                        (nb095AlphaDummy311 D R S_cls E) from (by
                                        unfold nb095AlphaDummy311;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0304 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from
                                      (by
                                        unfold nb095AlphaDummy312;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0305 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy311 D R S_cls E) from (by
                                          unfold nb095AlphaDummy311;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0304 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy309 f) ≠
        (nb095AlphaDummy312 f) from (by
                                          unfold nb095AlphaDummy312;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0305 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy311 D R S_cls E),
                                        (nb095AlphaDummy312 f)),
                                      ((nb095AlphaDummy307 D R S_cls E),
                                        (nb095AlphaDummy309 f)),
                                      ((nb095AlphaDummy308 D R S_cls E),
                                        (nb095AlphaDummy310 f)),
                                      ((nb095AlphaDummy333 D R S_cls E),
                                        (nb095AlphaDummy334 f)),
                                      ((nb095AlphaDummy331 D R S_cls E),
                                        (nb095AlphaDummy332 f)),
                                      ((nb095AlphaDummy300 D R S_cls E),
                                        (nb095AlphaDummy302 f)),
                                      ((nb095AlphaDummy299 D R S_cls E),
                                        (nb095AlphaDummy301 f)),
                                      ((nb095AlphaDummy329 D R S_cls E),
                                        (nb095AlphaDummy330 f)),
                                      ((nb095AlphaDummy303 D R S_cls E),
                                        (nb095AlphaDummy304 f)),
                                      ((nb095AlphaDummy296 D R S_cls E),
                                        (nb095AlphaDummy298 f)),
                                      ((nb095AlphaDummy295 D R S_cls E),
                                        (nb095AlphaDummy297 f)),
                                      ((nb095AlphaDummy293 D R S_cls E),
                                        (nb095AlphaDummy294 u S_cls f E)),
                                      ((nb095AlphaDummy291 D R S_cls E),
                                        (nb095AlphaDummy292 u S_cls f E)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
          [((nb095AlphaDummy331 D R S_cls E), (nb095AlphaDummy332 f)),
            ((nb095AlphaDummy300 D R S_cls E), (nb095AlphaDummy302 f)),
            ((nb095AlphaDummy299 D R S_cls E), (nb095AlphaDummy301 f)),
            ((nb095AlphaDummy329 D R S_cls E), (nb095AlphaDummy330 f)),
            ((nb095AlphaDummy303 D R S_cls E), (nb095AlphaDummy304 f)),
            ((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
            ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
            ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
            ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
            ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
            ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

theorem nb095_focused_notmem_0021 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy337 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        ((E).fv ∪ ((synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))).fv)
        0 ∉
      E.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb095_focused_notmem_0022 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy338 u S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        ((E).fv ∪ ((synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))).fv)
        0 ∉
      E.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb095_focused_notmem_0023 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy335 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((synCnin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv ∪ ((synCnin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin E
      (synCima (synCcnv (synCdif S_cls (synCid)))
        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0024 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy336 u S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((synCnin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv u))))).fv ∪ ((synCnin E
              (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin E
      (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0025 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy293 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((synCrn (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪ ((synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid)))
        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0026 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    (nb095AlphaDummy294 u S_cls f E) ∉ E.fv :=
  by
  change
    freshVar
        (((synCrn (Class.cv f))).fv ∪ ((synCin E
              (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0027 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy291 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((synCnin (synCrn (Class.cv (nb095AlphaDummy000 D R S_cls E))) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))).fv ∪
          ((synCnin (synCrn (Class.cv (nb095AlphaDummy000 D R S_cls E))) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin (synCrn (Class.cv (nb095AlphaDummy000 D R S_cls E)))
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
          (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid)))
        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0028 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    (nb095AlphaDummy292 u S_cls f E) ∉ E.fv :=
  by
  change
    freshVar
        (((synCnin (synCrn (Class.cv f)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))).fv ∪
          ((synCnin (synCrn (Class.cv f)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin (synCrn (Class.cv f))
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_compact_envfresh_0112 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_E_f : f ∉ E.fv) (dv_E_u : u ∉ E.fv)
    (dv_E_x : x ∉ E.fv) :
    TEnvFresh
      [((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      E.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095AlphaDummy337 D R S_cls E)
      (nb095AlphaDummy338 u S_cls E) (nb095_focused_notmem_0021 D R S_cls E)
      (nb095_focused_notmem_0022 u S_cls E)
      (TEnvFresh.consFresh (nb095AlphaDummy335 D R S_cls E)
        (nb095AlphaDummy336 u S_cls E) (nb095_focused_notmem_0023 D R S_cls E)
        (nb095_focused_notmem_0024 u S_cls E)
        (TEnvFresh.consFresh (nb095AlphaDummy293 D R S_cls E)
          (nb095AlphaDummy294 u S_cls f E) (nb095_focused_notmem_0025 D R S_cls E)
          (nb095_focused_notmem_0026 u S_cls f E)
          (TEnvFresh.consFresh (nb095AlphaDummy291 D R S_cls E)
            (nb095AlphaDummy292 u S_cls f E) (nb095_focused_notmem_0027 D R S_cls E)
            (nb095_focused_notmem_0028 u S_cls f E)
            (TEnvFresh.consFresh (nb095AlphaDummy001 D R S_cls E) u
              (nb095_focused_notmem_0002 D R S_cls E) dv_E_u
              (TEnvFresh.consFresh (nb095AlphaDummy002 D R S_cls E) x
                (nb095_focused_notmem_0003 D R S_cls E) dv_E_x
                (TEnvFresh.consFresh (nb095AlphaDummy000 D R S_cls E) f
                  (nb095_focused_notmem_0004 D R S_cls E) dv_E_f (TEnvFresh.nil E.fv))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
