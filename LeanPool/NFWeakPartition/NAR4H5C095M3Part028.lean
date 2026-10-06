/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C095M3Part028Stage1


/-! NF weak partition development: NAR4H5C095M3Part028. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_wpp_refl_0188`. -/
@[expose]
noncomputable def nb095WppRefl0188 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TReflOn
      [((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      ((synCid)).fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0192 x u D R S_cls f E)

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0057`. -/
@[expose]
noncomputable def nb095SplitAlpha0057 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy399 D R S_cls E), (nb095AlphaDummy400 f)),
        ((nb095AlphaDummy397 D R S_cls E), (nb095AlphaDummy398 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy399 D R S_cls E))
          (Class.cab (nb095AlphaDummy393 D R S_cls E)
            (synWrex (nb095AlphaDummy394 D R S_cls E)
              (Class.cv (nb095AlphaDummy385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy399 D R S_cls E))
            (Class.cab (nb095AlphaDummy393 D R S_cls E)
              (synWrex (nb095AlphaDummy394 D R S_cls E)
                (Class.cv (nb095AlphaDummy385 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy400 f))
          (Class.cab (nb095AlphaDummy395 f)
            (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy388 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                (synCphi (Class.cv (nb095AlphaDummy396 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy400 f))
            (Class.cab (nb095AlphaDummy395 f)
              (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy388 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                  (synCphi (Class.cv (nb095AlphaDummy396 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy385 D R S_cls E) ≠
                      (nb095AlphaDummy394 D R S_cls E) from (by
                      unfold nb095AlphaDummy394;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0394 D R S_cls E) 1))))
                  (show (nb095AlphaDummy388 f) ≠ (nb095AlphaDummy396 f) from (by
                      unfold nb095AlphaDummy396;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0396 f) 1))))
                  (TAlphaVar.there (show (nb095AlphaDummy385 D R S_cls E) ≠
                        (nb095AlphaDummy393 D R S_cls E) from (by
                        unfold nb095AlphaDummy393;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0394 D R S_cls E) 0))))
                    (show (nb095AlphaDummy388 f) ≠ (nb095AlphaDummy395 f) from (by
                        unfold nb095AlphaDummy395;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0396 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy385 D R S_cls E) ≠
                          (nb095AlphaDummy399 D R S_cls E) from (by
                          unfold nb095AlphaDummy399;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0398 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy388 f) ≠ (nb095AlphaDummy400 f) from (by
                          unfold nb095AlphaDummy400;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0399 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy385 D R S_cls E) ≠
                            (nb095AlphaDummy397 D R S_cls E) from (by
                            unfold nb095AlphaDummy397;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0395 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy388 f) ≠ (nb095AlphaDummy398 f) from (by
                            unfold nb095AlphaDummy398;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0397 f) 0))))
                        (TAlphaVar.there (freshVar_injective (((synCcnv
                                  (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪
                              ((synCcnv (synCcnv
                                    (Class.cv (nb095AlphaDummy000 D R S_cls E))))).fv)
                            (by decide)) (freshVar_injective (((synCcnv (Class.cv f))).fv ∪
                              ((synCcnv (synCcnv (Class.cv f)))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy388 f))).fv ∪
                      ((Class.cv (nb095AlphaDummy389 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy394 D R S_cls E) ≠
                              (nb095AlphaDummy401 D R S_cls E) from (by
                              unfold nb095AlphaDummy401;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0400 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy396 f) ≠ (nb095AlphaDummy403 f) from (by
                              unfold nb095AlphaDummy403;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0401 f) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy394 D R S_cls E) ≠
                                (nb095AlphaDummy402 D R S_cls E) from (by
                                unfold nb095AlphaDummy402;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0400 D R S_cls E) 1))))
                            (show (nb095AlphaDummy396 f) ≠ (nb095AlphaDummy404 f) from (by
                                unfold nb095AlphaDummy404;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0401 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy394 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy396 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy401 D R S_cls E) ≠
        (nb095AlphaDummy408 D R S_cls E) from (by
          unfold nb095AlphaDummy408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0404 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy403 f) ≠ (nb095AlphaDummy411 f) from (by
          unfold nb095AlphaDummy411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0405 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy401 D R S_cls E) ≠ (nb095AlphaDummy407 D R S_cls E) from (by
          unfold nb095AlphaDummy407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0404 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy403 f) ≠ (nb095AlphaDummy410 f) from (by
          unfold nb095AlphaDummy410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0405 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy401 D R S_cls E) ≠ (nb095AlphaDummy405 D R S_cls E) from (by
          unfold nb095AlphaDummy405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0402 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy403 f) ≠ (nb095AlphaDummy406 f) from (by
          unfold nb095AlphaDummy406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0403 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy409 D R S_cls E), (nb095AlphaDummy412 f)),
        ((nb095AlphaDummy408 D R S_cls E), (nb095AlphaDummy411 f)),
        ((nb095AlphaDummy407 D R S_cls E), (nb095AlphaDummy410 f)),
        ((nb095AlphaDummy405 D R S_cls E), (nb095AlphaDummy406 f)),
        ((nb095AlphaDummy401 D R S_cls E), (nb095AlphaDummy403 f)),
        ((nb095AlphaDummy402 D R S_cls E), (nb095AlphaDummy404 f)),
        ((nb095AlphaDummy394 D R S_cls E), (nb095AlphaDummy396 f)),
        ((nb095AlphaDummy393 D R S_cls E), (nb095AlphaDummy395 f)),
        ((nb095AlphaDummy399 D R S_cls E), (nb095AlphaDummy400 f)),
        ((nb095AlphaDummy397 D R S_cls E), (nb095AlphaDummy398 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy408
        D R S_cls E) ≠ (nb095AlphaDummy415 D R S_cls E) from (by
          unfold
            nb095AlphaDummy415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0408
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy411 f) ≠ (nb095AlphaDummy416 f) from (by
          unfold
            nb095AlphaDummy416;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0409
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy408 D R S_cls E) ≠
        (nb095AlphaDummy413 D R S_cls E) from (by
          unfold
            nb095AlphaDummy413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0406
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy411 f) ≠ (nb095AlphaDummy414 f) from (by
          unfold
            nb095AlphaDummy414;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0407
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy401
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy409 D R S_cls E) ≠ (nb095AlphaDummy415
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0412
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy412 f) ≠ (nb095AlphaDummy416 f) from (by
          unfold
            nb095AlphaDummy416;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0413
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy409 D R S_cls E) ≠
        (nb095AlphaDummy413 D R S_cls E) from (by
          unfold
            nb095AlphaDummy413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0410
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy412 f) ≠ (nb095AlphaDummy414 f) from (by
          unfold
            nb095AlphaDummy414;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0411
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy408 D R S_cls E) ≠ (nb095AlphaDummy415
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0408
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy411 f) ≠ (nb095AlphaDummy416 f) from (by
          unfold
            nb095AlphaDummy416;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0409
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy408 D R S_cls E) ≠
        (nb095AlphaDummy413 D R S_cls E) from (by
          unfold
            nb095AlphaDummy413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0406
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy411 f) ≠ (nb095AlphaDummy414 f) from (by
          unfold
            nb095AlphaDummy414;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0407
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy401
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy409 D R S_cls E) ≠ (nb095AlphaDummy415
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0412
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy412 f) ≠ (nb095AlphaDummy416 f) from (by
          unfold
            nb095AlphaDummy416;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0413
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy409 D R S_cls E) ≠
        (nb095AlphaDummy413 D R S_cls E) from (by
          unfold
            nb095AlphaDummy413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0410
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy412 f) ≠ (nb095AlphaDummy414 f) from (by
          unfold
            nb095AlphaDummy414;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0411
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy409 D R S_cls E), (nb095AlphaDummy412 f)),
        ((nb095AlphaDummy408 D R S_cls E), (nb095AlphaDummy411 f)),
        ((nb095AlphaDummy407 D R S_cls E), (nb095AlphaDummy410 f)),
        ((nb095AlphaDummy405 D R S_cls E), (nb095AlphaDummy406 f)),
        ((nb095AlphaDummy401 D R S_cls E), (nb095AlphaDummy403 f)),
        ((nb095AlphaDummy402 D R S_cls E), (nb095AlphaDummy404 f)),
        ((nb095AlphaDummy394 D R S_cls E), (nb095AlphaDummy396 f)),
        ((nb095AlphaDummy393 D R S_cls E), (nb095AlphaDummy395 f)),
        ((nb095AlphaDummy399 D R S_cls E), (nb095AlphaDummy400 f)),
        ((nb095AlphaDummy397 D R S_cls E), (nb095AlphaDummy398 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy401 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy401 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy408 D R S_cls E) ≠ (nb095AlphaDummy419
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy419;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0416
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy411 f) ≠ (nb095AlphaDummy420 f) from (by
          unfold
            nb095AlphaDummy420;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0417
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy408 D R S_cls E) ≠
        (nb095AlphaDummy417 D R S_cls E) from (by
          unfold
            nb095AlphaDummy417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0414
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy411 f) ≠ (nb095AlphaDummy418 f) from (by
          unfold
            nb095AlphaDummy418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0415
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy401
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy408 D R S_cls E) ≠ (nb095AlphaDummy419
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy419;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0416
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy411 f) ≠ (nb095AlphaDummy420 f) from (by
          unfold
            nb095AlphaDummy420;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0417
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy408 D R S_cls E) ≠
        (nb095AlphaDummy417 D R S_cls E) from (by
          unfold
            nb095AlphaDummy417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0414
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy411 f) ≠ (nb095AlphaDummy418 f) from (by
          unfold
            nb095AlphaDummy418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0415
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy401
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy409
        D R S_cls E) ≠ (nb095AlphaDummy421 D R S_cls E) from (by
          unfold
            nb095AlphaDummy421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0420
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy412 f) ≠ (nb095AlphaDummy422 f) from (by
          unfold
            nb095AlphaDummy422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0421
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy409 D R S_cls E) ≠
        (nb095AlphaDummy417 D R S_cls E) from (by
          unfold
            nb095AlphaDummy417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0418
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy412 f) ≠ (nb095AlphaDummy418 f) from (by
          unfold
            nb095AlphaDummy418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0419
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy409
        D R S_cls E) ≠ (nb095AlphaDummy421 D R S_cls E) from (by
          unfold
            nb095AlphaDummy421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0420
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy412 f) ≠ (nb095AlphaDummy422 f) from (by
          unfold
            nb095AlphaDummy422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0421
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy409 D R S_cls E) ≠
        (nb095AlphaDummy417 D R S_cls E) from (by
          unfold
            nb095AlphaDummy417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0418
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy412 f) ≠ (nb095AlphaDummy418 f) from (by
          unfold
            nb095AlphaDummy418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0419
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy401 D R S_cls E) ≠
                                        (nb095AlphaDummy405 D R S_cls E) from (by
                                        unfold nb095AlphaDummy405;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0402 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy403 f) ≠ (nb095AlphaDummy406 f) from
                                      (by
                                        unfold nb095AlphaDummy406;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0403 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy405 D R S_cls E),
                                      (nb095AlphaDummy406 f)),
                                    ((nb095AlphaDummy401 D R S_cls E),
                                      (nb095AlphaDummy403 f)),
                                    ((nb095AlphaDummy402 D R S_cls E),
                                      (nb095AlphaDummy404 f)),
                                    ((nb095AlphaDummy394 D R S_cls E),
                                      (nb095AlphaDummy396 f)),
                                    ((nb095AlphaDummy393 D R S_cls E),
                                      (nb095AlphaDummy395 f)),
                                    ((nb095AlphaDummy399 D R S_cls E),
                                      (nb095AlphaDummy400 f)),
                                    ((nb095AlphaDummy397 D R S_cls E),
                                      (nb095AlphaDummy398 f)),
                                    ((nb095AlphaDummy386 D R S_cls E),
                                      (nb095AlphaDummy389 f)),
                                    ((nb095AlphaDummy385 D R S_cls E),
                                      (nb095AlphaDummy388 f)),
                                    ((nb095AlphaDummy391 D R S_cls E),
                                      (nb095AlphaDummy392 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy401 D R S_cls E) ≠
                                      (nb095AlphaDummy405 D R S_cls E) from (by
                                      unfold nb095AlphaDummy405;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0402 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy403 f) ≠ (nb095AlphaDummy406 f) from
                                    (by
                                      unfold nb095AlphaDummy406;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0403 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy401 D R S_cls E) ≠
                                        (nb095AlphaDummy405 D R S_cls E) from (by
                                        unfold nb095AlphaDummy405;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0402 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy403 f) ≠ (nb095AlphaDummy406 f) from
                                      (by
                                        unfold nb095AlphaDummy406;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0403 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy405 D R S_cls E),
                                      (nb095AlphaDummy406 f)),
                                    ((nb095AlphaDummy401 D R S_cls E),
                                      (nb095AlphaDummy403 f)),
                                    ((nb095AlphaDummy402 D R S_cls E),
                                      (nb095AlphaDummy404 f)),
                                    ((nb095AlphaDummy394 D R S_cls E),
                                      (nb095AlphaDummy396 f)),
                                    ((nb095AlphaDummy393 D R S_cls E),
                                      (nb095AlphaDummy395 f)),
                                    ((nb095AlphaDummy399 D R S_cls E),
                                      (nb095AlphaDummy400 f)),
                                    ((nb095AlphaDummy397 D R S_cls E),
                                      (nb095AlphaDummy398 f)),
                                    ((nb095AlphaDummy386 D R S_cls E),
                                      (nb095AlphaDummy389 f)),
                                    ((nb095AlphaDummy385 D R S_cls E),
                                      (nb095AlphaDummy388 f)),
                                    ((nb095AlphaDummy391 D R S_cls E),
                                      (nb095AlphaDummy392 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095AlphaDummy385 D R S_cls E) ≠
                        (nb095AlphaDummy394 D R S_cls E) from (by
                        unfold nb095AlphaDummy394;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0394 D R S_cls E) 1))))
                    (show (nb095AlphaDummy388 f) ≠ (nb095AlphaDummy396 f) from (by
                        unfold nb095AlphaDummy396;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0396 f) 1)))) (TAlphaVar.there
                      (show (nb095AlphaDummy385 D R S_cls E) ≠
                          (nb095AlphaDummy393 D R S_cls E) from (by
                          unfold nb095AlphaDummy393;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0394 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy388 f) ≠ (nb095AlphaDummy395 f) from (by
                          unfold nb095AlphaDummy395;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0396 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy385 D R S_cls E) ≠
                            (nb095AlphaDummy399 D R S_cls E) from (by
                            unfold nb095AlphaDummy399;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0398 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy388 f) ≠ (nb095AlphaDummy400 f) from (by
                            unfold nb095AlphaDummy400;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0399 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy385 D R S_cls E) ≠
                              (nb095AlphaDummy397 D R S_cls E) from (by
                              unfold nb095AlphaDummy397;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0395 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy388 f) ≠ (nb095AlphaDummy398 f) from (by
                              unfold nb095AlphaDummy398;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0397 f) 0))))
                          (TAlphaVar.there (freshVar_injective (((synCcnv
                                    (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪
                                ((synCcnv (synCcnv (Class.cv
                                        (nb095AlphaDummy000 D R S_cls E))))).fv) (by decide))
                            (freshVar_injective (((synCcnv (Class.cv f))).fv ∪
                                ((synCcnv (synCcnv (Class.cv f)))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy388 f))).fv ∪
                        ((Class.cv (nb095AlphaDummy389 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy394 D R S_cls E) ≠
                                (nb095AlphaDummy401 D R S_cls E) from (by
                                unfold nb095AlphaDummy401;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0400 D R S_cls E) 0))))
                            (show (nb095AlphaDummy396 f) ≠ (nb095AlphaDummy403 f) from (by
                                unfold nb095AlphaDummy403;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0401 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy394 D R S_cls E) ≠
                                  (nb095AlphaDummy402 D R S_cls E) from (by
                                  unfold nb095AlphaDummy402;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0400 D R S_cls E) 1))))
                              (show (nb095AlphaDummy396 f) ≠ (nb095AlphaDummy404 f) from
                                (by
                                  unfold nb095AlphaDummy404;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0401 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy394 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy396 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy401 D R S_cls E) ≠ (nb095AlphaDummy408 D R S_cls E) from (by
          unfold nb095AlphaDummy408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0404 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy403 f) ≠ (nb095AlphaDummy411 f) from (by
          unfold nb095AlphaDummy411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0405 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy401 D R S_cls E) ≠ (nb095AlphaDummy407 D R S_cls E) from (by
          unfold nb095AlphaDummy407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0404 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy403 f) ≠ (nb095AlphaDummy410 f) from (by
          unfold nb095AlphaDummy410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0405 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy401 D R S_cls E) ≠
        (nb095AlphaDummy405 D R S_cls E) from (by
          unfold nb095AlphaDummy405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0402 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy403 f) ≠ (nb095AlphaDummy406 f) from (by
          unfold nb095AlphaDummy406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0403 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy409 D R S_cls E), (nb095AlphaDummy412 f)),
        ((nb095AlphaDummy408 D R S_cls E), (nb095AlphaDummy411 f)),
        ((nb095AlphaDummy407 D R S_cls E), (nb095AlphaDummy410 f)),
        ((nb095AlphaDummy405 D R S_cls E), (nb095AlphaDummy406 f)),
        ((nb095AlphaDummy401 D R S_cls E), (nb095AlphaDummy403 f)),
        ((nb095AlphaDummy402 D R S_cls E), (nb095AlphaDummy404 f)),
        ((nb095AlphaDummy394 D R S_cls E), (nb095AlphaDummy396 f)),
        ((nb095AlphaDummy393 D R S_cls E), (nb095AlphaDummy395 f)),
        ((nb095AlphaDummy399 D R S_cls E), (nb095AlphaDummy400 f)),
        ((nb095AlphaDummy397 D R S_cls E), (nb095AlphaDummy398 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy408
        D R S_cls E) ≠ (nb095AlphaDummy415 D R S_cls E) from (by
          unfold
            nb095AlphaDummy415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0408
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy411 f) ≠ (nb095AlphaDummy416 f) from (by
          unfold
            nb095AlphaDummy416;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0409
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy408 D R S_cls E) ≠
        (nb095AlphaDummy413 D R S_cls E) from (by
          unfold
            nb095AlphaDummy413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0406
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy411 f) ≠ (nb095AlphaDummy414 f) from (by
          unfold
            nb095AlphaDummy414;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0407
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy401
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy409 D R S_cls E) ≠ (nb095AlphaDummy415
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0412
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy412 f) ≠ (nb095AlphaDummy416 f) from (by
          unfold
            nb095AlphaDummy416;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0413
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy409 D R S_cls E) ≠
        (nb095AlphaDummy413 D R S_cls E) from (by
          unfold
            nb095AlphaDummy413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0410
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy412 f) ≠ (nb095AlphaDummy414 f) from (by
          unfold
            nb095AlphaDummy414;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0411
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy408 D R S_cls E) ≠ (nb095AlphaDummy415
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0408
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy411 f) ≠ (nb095AlphaDummy416 f) from (by
          unfold
            nb095AlphaDummy416;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0409
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy408 D R S_cls E) ≠
        (nb095AlphaDummy413 D R S_cls E) from (by
          unfold
            nb095AlphaDummy413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0406
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy411 f) ≠ (nb095AlphaDummy414 f) from (by
          unfold
            nb095AlphaDummy414;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0407
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy401
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy409 D R S_cls E) ≠ (nb095AlphaDummy415
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0412
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy412 f) ≠ (nb095AlphaDummy416 f) from (by
          unfold
            nb095AlphaDummy416;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0413
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy409 D R S_cls E) ≠
        (nb095AlphaDummy413 D R S_cls E) from (by
          unfold
            nb095AlphaDummy413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0410
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy412 f) ≠ (nb095AlphaDummy414 f) from (by
          unfold
            nb095AlphaDummy414;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0411
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy409 D R S_cls E), (nb095AlphaDummy412 f)),
        ((nb095AlphaDummy408 D R S_cls E), (nb095AlphaDummy411 f)),
        ((nb095AlphaDummy407 D R S_cls E), (nb095AlphaDummy410 f)),
        ((nb095AlphaDummy405 D R S_cls E), (nb095AlphaDummy406 f)),
        ((nb095AlphaDummy401 D R S_cls E), (nb095AlphaDummy403 f)),
        ((nb095AlphaDummy402 D R S_cls E), (nb095AlphaDummy404 f)),
        ((nb095AlphaDummy394 D R S_cls E), (nb095AlphaDummy396 f)),
        ((nb095AlphaDummy393 D R S_cls E), (nb095AlphaDummy395 f)),
        ((nb095AlphaDummy399 D R S_cls E), (nb095AlphaDummy400 f)),
        ((nb095AlphaDummy397 D R S_cls E), (nb095AlphaDummy398 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy401 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy401 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy408 D R S_cls E) ≠ (nb095AlphaDummy419
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy419;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0416
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy411 f) ≠ (nb095AlphaDummy420 f) from (by
          unfold
            nb095AlphaDummy420;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0417
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy408 D R S_cls E) ≠
        (nb095AlphaDummy417 D R S_cls E) from (by
          unfold
            nb095AlphaDummy417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0414
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy411 f) ≠ (nb095AlphaDummy418 f) from (by
          unfold
            nb095AlphaDummy418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0415
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy401
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy408 D R S_cls E) ≠ (nb095AlphaDummy419
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy419;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0416
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy411 f) ≠ (nb095AlphaDummy420 f) from (by
          unfold
            nb095AlphaDummy420;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0417
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy408 D R S_cls E) ≠
        (nb095AlphaDummy417 D R S_cls E) from (by
          unfold
            nb095AlphaDummy417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0414
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy411 f) ≠ (nb095AlphaDummy418 f) from (by
          unfold
            nb095AlphaDummy418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0415
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy401
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy409
        D R S_cls E) ≠ (nb095AlphaDummy421 D R S_cls E) from (by
          unfold
            nb095AlphaDummy421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0420
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy412 f) ≠ (nb095AlphaDummy422 f) from (by
          unfold
            nb095AlphaDummy422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0421
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy409 D R S_cls E) ≠
        (nb095AlphaDummy417 D R S_cls E) from (by
          unfold
            nb095AlphaDummy417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0418
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy412 f) ≠ (nb095AlphaDummy418 f) from (by
          unfold
            nb095AlphaDummy418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0419
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy409
        D R S_cls E) ≠ (nb095AlphaDummy421 D R S_cls E) from (by
          unfold
            nb095AlphaDummy421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0420
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy412 f) ≠ (nb095AlphaDummy422 f) from (by
          unfold
            nb095AlphaDummy422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0421
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy409 D R S_cls E) ≠
        (nb095AlphaDummy417 D R S_cls E) from (by
          unfold
            nb095AlphaDummy417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0418
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy412 f) ≠ (nb095AlphaDummy418 f) from (by
          unfold
            nb095AlphaDummy418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0419
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy401 D R S_cls E) ≠
        (nb095AlphaDummy405 D R S_cls E) from (by
                                          unfold nb095AlphaDummy405;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0402 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy403 f) ≠
        (nb095AlphaDummy406 f) from (by
                                          unfold nb095AlphaDummy406;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0403 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy405 D R S_cls E),
                                        (nb095AlphaDummy406 f)),
                                      ((nb095AlphaDummy401 D R S_cls E),
                                        (nb095AlphaDummy403 f)),
                                      ((nb095AlphaDummy402 D R S_cls E),
                                        (nb095AlphaDummy404 f)),
                                      ((nb095AlphaDummy394 D R S_cls E),
                                        (nb095AlphaDummy396 f)),
                                      ((nb095AlphaDummy393 D R S_cls E),
                                        (nb095AlphaDummy395 f)),
                                      ((nb095AlphaDummy399 D R S_cls E),
                                        (nb095AlphaDummy400 f)),
                                      ((nb095AlphaDummy397 D R S_cls E),
                                        (nb095AlphaDummy398 f)),
                                      ((nb095AlphaDummy386 D R S_cls E),
                                        (nb095AlphaDummy389 f)),
                                      ((nb095AlphaDummy385 D R S_cls E),
                                        (nb095AlphaDummy388 f)),
                                      ((nb095AlphaDummy391 D R S_cls E),
                                        (nb095AlphaDummy392 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy401 D R S_cls E) ≠
                                        (nb095AlphaDummy405 D R S_cls E) from (by
                                        unfold nb095AlphaDummy405;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0402 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy403 f) ≠ (nb095AlphaDummy406 f) from
                                      (by
                                        unfold nb095AlphaDummy406;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0403 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy401 D R S_cls E) ≠
        (nb095AlphaDummy405 D R S_cls E) from (by
                                          unfold nb095AlphaDummy405;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0402 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy403 f) ≠
        (nb095AlphaDummy406 f) from (by
                                          unfold nb095AlphaDummy406;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0403 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy405 D R S_cls E),
                                        (nb095AlphaDummy406 f)),
                                      ((nb095AlphaDummy401 D R S_cls E),
                                        (nb095AlphaDummy403 f)),
                                      ((nb095AlphaDummy402 D R S_cls E),
                                        (nb095AlphaDummy404 f)),
                                      ((nb095AlphaDummy394 D R S_cls E),
                                        (nb095AlphaDummy396 f)),
                                      ((nb095AlphaDummy393 D R S_cls E),
                                        (nb095AlphaDummy395 f)),
                                      ((nb095AlphaDummy399 D R S_cls E),
                                        (nb095AlphaDummy400 f)),
                                      ((nb095AlphaDummy397 D R S_cls E),
                                        (nb095AlphaDummy398 f)),
                                      ((nb095AlphaDummy386 D R S_cls E),
                                        (nb095AlphaDummy389 f)),
                                      ((nb095AlphaDummy385 D R S_cls E),
                                        (nb095AlphaDummy388 f)),
                                      ((nb095AlphaDummy391 D R S_cls E),
                                        (nb095AlphaDummy392 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
