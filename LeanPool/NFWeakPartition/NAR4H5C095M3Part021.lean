/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part020

/-! NF weak partition development: NAR4H5C095M3Part021. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0034`. -/
@[expose]
noncomputable def nb095SplitAlpha0034 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_E_f : f ∉ E.fv) (dv_E_u : u ∉ E.fv)
    (dv_E_x : x ∉ E.fv) (dv_S_f : f ∉ S_cls.fv) (dv_S_u : u ∉ S_cls.fv)
    (dv_S_x : x ∉ S_cls.fv) (dv_f_u : f ≠ u) (dv_f_x : f ≠ x) :
    TAlphaWff
      [((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy291 D R S_cls E))
          (synCnin (synCrn (Class.cv (nb095AlphaDummy000 D R S_cls E))) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy291 D R S_cls E))
            (synCnin (synCrn (Class.cv (nb095AlphaDummy000 D R S_cls E))) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy292 u S_cls f E))
          (synCnin (synCrn (Class.cv f)) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))))
        (Wff.neg (Wff.classMem (Class.cv (nb095AlphaDummy292 u S_cls f E))
            (synCnin (synCrn (Class.cv f)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
                          ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
                          ((nb095AlphaDummy293 D R S_cls E),
                            (nb095AlphaDummy294 u S_cls f E)),
                          ((nb095AlphaDummy291 D R S_cls E),
                            (nb095AlphaDummy292 u S_cls f E)),
                          ((nb095AlphaDummy001 D R S_cls E), u),
                          ((nb095AlphaDummy002 D R S_cls E), x),
                          ((nb095AlphaDummy000 D R S_cls E), f)]
                        (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb095SplitAlpha0030 x u D R S_cls f E)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy295 D R S_cls E) ≠
        (nb095AlphaDummy300 D R S_cls E) from (by
          unfold nb095AlphaDummy300;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0324 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy302 f) from (by
          unfold nb095AlphaDummy302;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0326 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy295 D R S_cls E) ≠
        (nb095AlphaDummy299 D R S_cls E) from (by
          unfold nb095AlphaDummy299;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0324 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy301 f) from (by
          unfold nb095AlphaDummy301;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0326 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy295 D R S_cls E) ≠
        (nb095AlphaDummy329 D R S_cls E) from (by
          unfold nb095AlphaDummy329;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0328
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy330 f) from (by
          unfold nb095AlphaDummy330;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0329
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy295 D R S_cls E) ≠
        (nb095AlphaDummy303 D R S_cls E) from (by
          unfold nb095AlphaDummy303;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0325
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy304 f) from (by
          unfold nb095AlphaDummy304;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0327
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCvv)).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv ∪ ((synCvv)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095AlphaDummy296 D R S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy295 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy298 f))).fv ∪ ((Class.cv (nb095AlphaDummy297 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb095SplitAlpha0031 x u D R S_cls f
        E))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy295 D R S_cls E) ≠ (nb095AlphaDummy300 D R S_cls E) from (by
          unfold nb095AlphaDummy300;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0324 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy302 f) from (by
          unfold nb095AlphaDummy302;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0326 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy295 D R S_cls E) ≠
        (nb095AlphaDummy299 D R S_cls E) from (by
          unfold nb095AlphaDummy299;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0324 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy301 f) from (by
          unfold nb095AlphaDummy301;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0326 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy295 D R S_cls E) ≠
        (nb095AlphaDummy329 D R S_cls E) from (by
          unfold nb095AlphaDummy329;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0328
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy330 f) from (by
          unfold nb095AlphaDummy330;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0329
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy295 D R S_cls E) ≠
        (nb095AlphaDummy303 D R S_cls E) from (by
          unfold nb095AlphaDummy303;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0325
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy304 f) from (by
          unfold nb095AlphaDummy304;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0327
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCvv)).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv ∪ ((synCvv)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095AlphaDummy296 D R S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy295 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy298 f))).fv ∪ ((Class.cv (nb095AlphaDummy297 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb095SplitAlpha0031 x u D R S_cls f
        E)))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                            (nb095AlphaDummy000 D R S_cls E) ≠
                              (nb095AlphaDummy296 D R S_cls E) from (by
                              unfold nb095AlphaDummy296;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0338 D R S_cls E)
                                      1)))) (show f ≠ (nb095AlphaDummy298 f) from (by
                              unfold nb095AlphaDummy298;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0339 f) 1))))
                          (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                (nb095AlphaDummy295 D R S_cls E) from (by
                                unfold nb095AlphaDummy295;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0338 D R S_cls E) 0))))
                            (show f ≠ (nb095AlphaDummy297 f) from (by
                                unfold nb095AlphaDummy297;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0339 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                  (nb095AlphaDummy293 D R S_cls E) from (by
                                  unfold nb095AlphaDummy293;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0336 D R S_cls E) 0))))
                              (show f ≠ (nb095AlphaDummy294 u S_cls f E) from (by
                                  unfold nb095AlphaDummy294;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0337 u S_cls f E) 0))))
                              (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                    (nb095AlphaDummy291 D R S_cls E) from (by
                                    unfold nb095AlphaDummy291;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0334 D R S_cls E) 0))))
                                (show f ≠ (nb095AlphaDummy292 u S_cls f E) from (by
                                    unfold nb095AlphaDummy292;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0335 u S_cls f E) 0))))
                                (TAlphaVar.there (freshVar_injective
                                    ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_u
                                  (TAlphaVar.there (freshVar_injective
                                      ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide))
                                    dv_f_x (TAlphaVar.here _ _ _)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfReflOn [((nb095AlphaDummy337 D R S_cls E),
                                    (nb095AlphaDummy338 u S_cls E)),
                                  ((nb095AlphaDummy335 D R S_cls E),
                                    (nb095AlphaDummy336 u S_cls E)),
                                  ((nb095AlphaDummy293 D R S_cls E),
                                    (nb095AlphaDummy294 u S_cls f E)),
                                  ((nb095AlphaDummy291 D R S_cls E),
                                    (nb095AlphaDummy292 u S_cls f E)),
                                  ((nb095AlphaDummy001 D R S_cls E), u),
                                  ((nb095AlphaDummy002 D R S_cls E), x),
                                  ((nb095AlphaDummy000 D R S_cls E), f)] E
                                (nb095FocusedRefl0003 x u D R S_cls f E dv_E_f dv_E_u
                                  dv_E_x)))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy001 D R S_cls E) ≠ (nb095AlphaDummy343 D R S_cls E) from (by
          unfold nb095AlphaDummy343;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0350 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy344 u) from (by
          unfold nb095AlphaDummy344;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0351 u) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy001 D R S_cls E) ≠ (nb095AlphaDummy340 D R S_cls E) from (by
          unfold nb095AlphaDummy340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R
                    S_cls E)
                  1)))) (show u ≠ (nb095AlphaDummy342 u S_cls) from (by
          unfold nb095AlphaDummy342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0349 u
                    S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy339 D R S_cls E) from (by
          unfold nb095AlphaDummy339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy341 u S_cls) from (by
          unfold nb095AlphaDummy341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0349 u
                    S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy337 D R S_cls E) from (by
          unfold nb095AlphaDummy337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0346 D
                    R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy338 u S_cls E) from (by
          unfold nb095AlphaDummy338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0347 u
                    S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy335 D R S_cls E) from (by
          unfold nb095AlphaDummy335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0344
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy336 u S_cls E) from (by
          unfold nb095AlphaDummy336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0345
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy293 D R S_cls E) from (by
          unfold nb095AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0342
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy294 u S_cls f E) from (by
          unfold nb095AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0343
                    u S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy291 D R S_cls E) from (by
          unfold
            nb095AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0340
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy292 u S_cls f E) from (by
          unfold
            nb095AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0341
                    u S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0032 x u D R S_cls f E))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy339
        D R S_cls E) ≠ (nb095AlphaDummy346 D R S_cls E) from (by
          unfold
            nb095AlphaDummy346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy348 u S_cls)
        from (by
          unfold
            nb095AlphaDummy348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy345 D R S_cls E) from (by
          unfold
            nb095AlphaDummy345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy347 u S_cls)
        from (by
          unfold
            nb095AlphaDummy347;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy375 D R S_cls E) from (by
          unfold
            nb095AlphaDummy375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0384
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy376 u S_cls)
        from (by
          unfold
            nb095AlphaDummy376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0385
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy349 D R S_cls E) from (by
          unfold
            nb095AlphaDummy349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0381
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy350 u S_cls)
        from (by
          unfold
            nb095AlphaDummy350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0383
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif S_cls
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn
        (Class.cv u))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy340
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪ ((Class.cv
        (nb095AlphaDummy341 u S_cls))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (nb095SplitAlpha0033
        x u D R S_cls f E) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb095AlphaDummy377 D R S_cls E),
        (nb095AlphaDummy378 u S_cls)), ((nb095AlphaDummy346 D R S_cls E),
        (nb095AlphaDummy348 u S_cls)), ((nb095AlphaDummy345 D R S_cls E),
        (nb095AlphaDummy347 u S_cls)), ((nb095AlphaDummy375 D R S_cls E),
        (nb095AlphaDummy376 u S_cls)), ((nb095AlphaDummy349 D R S_cls E),
        (nb095AlphaDummy350 u S_cls)), ((nb095AlphaDummy340 D R S_cls E),
        (nb095AlphaDummy342 u S_cls)), ((nb095AlphaDummy339 D R S_cls E),
        (nb095AlphaDummy341 u S_cls)), ((nb095AlphaDummy337 D R S_cls E),
        (nb095AlphaDummy338 u S_cls E)), ((nb095AlphaDummy335 D R S_cls E),
        (nb095AlphaDummy336 u S_cls E)), ((nb095AlphaDummy293 D R S_cls E),
        (nb095AlphaDummy294 u S_cls f E)), ((nb095AlphaDummy291 D R S_cls E),
        (nb095AlphaDummy292 u S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy339
        D R S_cls E) ≠ (nb095AlphaDummy346 D R S_cls E) from (by
          unfold
            nb095AlphaDummy346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy348 u S_cls)
        from (by
          unfold
            nb095AlphaDummy348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy345 D R S_cls E) from (by
          unfold
            nb095AlphaDummy345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy347 u S_cls)
        from (by
          unfold
            nb095AlphaDummy347;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy375 D R S_cls E) from (by
          unfold
            nb095AlphaDummy375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0384
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy376 u S_cls)
        from (by
          unfold
            nb095AlphaDummy376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0385
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy349 D R S_cls E) from (by
          unfold
            nb095AlphaDummy349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0381
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy350 u S_cls)
        from (by
          unfold
            nb095AlphaDummy350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0383
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif S_cls
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn
        (Class.cv u))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy340
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪ ((Class.cv
        (nb095AlphaDummy341 u S_cls))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (nb095SplitAlpha0033
        x u D R S_cls f E) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb095AlphaDummy377 D R S_cls E),
        (nb095AlphaDummy378 u S_cls)), ((nb095AlphaDummy346 D R S_cls E),
        (nb095AlphaDummy348 u S_cls)), ((nb095AlphaDummy345 D R S_cls E),
        (nb095AlphaDummy347 u S_cls)), ((nb095AlphaDummy375 D R S_cls E),
        (nb095AlphaDummy376 u S_cls)), ((nb095AlphaDummy349 D R S_cls E),
        (nb095AlphaDummy350 u S_cls)), ((nb095AlphaDummy340 D R S_cls E),
        (nb095AlphaDummy342 u S_cls)), ((nb095AlphaDummy339 D R S_cls E),
        (nb095AlphaDummy341 u S_cls)), ((nb095AlphaDummy337 D R S_cls E),
        (nb095AlphaDummy338 u S_cls E)), ((nb095AlphaDummy335 D R S_cls E),
        (nb095AlphaDummy336 u S_cls E)), ((nb095AlphaDummy293 D R S_cls E),
        (nb095AlphaDummy294 u S_cls f E)), ((nb095AlphaDummy291 D R S_cls E),
        (nb095AlphaDummy292 u S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                                        [((nb095AlphaDummy340 D R S_cls E),
        (nb095AlphaDummy342 u S_cls)), ((nb095AlphaDummy339 D R S_cls E),
        (nb095AlphaDummy341 u S_cls)), ((nb095AlphaDummy337 D R S_cls E),
        (nb095AlphaDummy338 u S_cls E)), ((nb095AlphaDummy335 D R S_cls E),
        (nb095AlphaDummy336 u S_cls E)), ((nb095AlphaDummy293 D R S_cls E),
        (nb095AlphaDummy294 u S_cls f E)), ((nb095AlphaDummy291 D R S_cls E),
        (nb095AlphaDummy292 u S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
                                        (synCcnv (synCdif S_cls (synCid)))
                                        (nb095WppRefl0116 x u D R S_cls f E dv_S_f
        dv_S_u dv_S_x))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfReflOn [((nb095AlphaDummy337 D R S_cls E),
                                    (nb095AlphaDummy338 u S_cls E)),
                                  ((nb095AlphaDummy335 D R S_cls E),
                                    (nb095AlphaDummy336 u S_cls E)),
                                  ((nb095AlphaDummy293 D R S_cls E),
                                    (nb095AlphaDummy294 u S_cls f E)),
                                  ((nb095AlphaDummy291 D R S_cls E),
                                    (nb095AlphaDummy292 u S_cls f E)),
                                  ((nb095AlphaDummy001 D R S_cls E), u),
                                  ((nb095AlphaDummy002 D R S_cls E), x),
                                  ((nb095AlphaDummy000 D R S_cls E), f)] E
                                (nb095FocusedRefl0003 x u D R S_cls f E dv_E_f dv_E_u
                                  dv_E_x)))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy001 D R S_cls E) ≠ (nb095AlphaDummy343 D R S_cls E) from (by
          unfold nb095AlphaDummy343;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0350 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy344 u) from (by
          unfold nb095AlphaDummy344;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0351 u) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy001 D R S_cls E) ≠ (nb095AlphaDummy340 D R S_cls E) from (by
          unfold nb095AlphaDummy340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R
                    S_cls E)
                  1)))) (show u ≠ (nb095AlphaDummy342 u S_cls) from (by
          unfold nb095AlphaDummy342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0349 u
                    S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy339 D R S_cls E) from (by
          unfold nb095AlphaDummy339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy341 u S_cls) from (by
          unfold nb095AlphaDummy341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0349 u
                    S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy337 D R S_cls E) from (by
          unfold nb095AlphaDummy337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0346 D
                    R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy338 u S_cls E) from (by
          unfold nb095AlphaDummy338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0347 u
                    S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy335 D R S_cls E) from (by
          unfold nb095AlphaDummy335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0344
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy336 u S_cls E) from (by
          unfold nb095AlphaDummy336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0345
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy293 D R S_cls E) from (by
          unfold nb095AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0342
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy294 u S_cls f E) from (by
          unfold nb095AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0343
                    u S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy291 D R S_cls E) from (by
          unfold
            nb095AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0340
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy292 u S_cls f E) from (by
          unfold
            nb095AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0341
                    u S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0032 x u D R S_cls f E))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy339
        D R S_cls E) ≠ (nb095AlphaDummy346 D R S_cls E) from (by
          unfold
            nb095AlphaDummy346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy348 u S_cls)
        from (by
          unfold
            nb095AlphaDummy348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy345 D R S_cls E) from (by
          unfold
            nb095AlphaDummy345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy347 u S_cls)
        from (by
          unfold
            nb095AlphaDummy347;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy375 D R S_cls E) from (by
          unfold
            nb095AlphaDummy375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0384
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy376 u S_cls)
        from (by
          unfold
            nb095AlphaDummy376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0385
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy349 D R S_cls E) from (by
          unfold
            nb095AlphaDummy349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0381
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy350 u S_cls)
        from (by
          unfold
            nb095AlphaDummy350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0383
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif S_cls
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn
        (Class.cv u))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy340
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪ ((Class.cv
        (nb095AlphaDummy341 u S_cls))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (nb095SplitAlpha0033
        x u D R S_cls f E) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb095AlphaDummy377 D R S_cls E),
        (nb095AlphaDummy378 u S_cls)), ((nb095AlphaDummy346 D R S_cls E),
        (nb095AlphaDummy348 u S_cls)), ((nb095AlphaDummy345 D R S_cls E),
        (nb095AlphaDummy347 u S_cls)), ((nb095AlphaDummy375 D R S_cls E),
        (nb095AlphaDummy376 u S_cls)), ((nb095AlphaDummy349 D R S_cls E),
        (nb095AlphaDummy350 u S_cls)), ((nb095AlphaDummy340 D R S_cls E),
        (nb095AlphaDummy342 u S_cls)), ((nb095AlphaDummy339 D R S_cls E),
        (nb095AlphaDummy341 u S_cls)), ((nb095AlphaDummy337 D R S_cls E),
        (nb095AlphaDummy338 u S_cls E)), ((nb095AlphaDummy335 D R S_cls E),
        (nb095AlphaDummy336 u S_cls E)), ((nb095AlphaDummy293 D R S_cls E),
        (nb095AlphaDummy294 u S_cls f E)), ((nb095AlphaDummy291 D R S_cls E),
        (nb095AlphaDummy292 u S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy339
        D R S_cls E) ≠ (nb095AlphaDummy346 D R S_cls E) from (by
          unfold
            nb095AlphaDummy346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy348 u S_cls)
        from (by
          unfold
            nb095AlphaDummy348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy345 D R S_cls E) from (by
          unfold
            nb095AlphaDummy345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy347 u S_cls)
        from (by
          unfold
            nb095AlphaDummy347;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy375 D R S_cls E) from (by
          unfold
            nb095AlphaDummy375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0384
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy376 u S_cls)
        from (by
          unfold
            nb095AlphaDummy376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0385
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy349 D R S_cls E) from (by
          unfold
            nb095AlphaDummy349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0381
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy350 u S_cls)
        from (by
          unfold
            nb095AlphaDummy350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0383
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif S_cls
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn
        (Class.cv u))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy340
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪ ((Class.cv
        (nb095AlphaDummy341 u S_cls))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (nb095SplitAlpha0033
        x u D R S_cls f E) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb095AlphaDummy377 D R S_cls E),
        (nb095AlphaDummy378 u S_cls)), ((nb095AlphaDummy346 D R S_cls E),
        (nb095AlphaDummy348 u S_cls)), ((nb095AlphaDummy345 D R S_cls E),
        (nb095AlphaDummy347 u S_cls)), ((nb095AlphaDummy375 D R S_cls E),
        (nb095AlphaDummy376 u S_cls)), ((nb095AlphaDummy349 D R S_cls E),
        (nb095AlphaDummy350 u S_cls)), ((nb095AlphaDummy340 D R S_cls E),
        (nb095AlphaDummy342 u S_cls)), ((nb095AlphaDummy339 D R S_cls E),
        (nb095AlphaDummy341 u S_cls)), ((nb095AlphaDummy337 D R S_cls E),
        (nb095AlphaDummy338 u S_cls E)), ((nb095AlphaDummy335 D R S_cls E),
        (nb095AlphaDummy336 u S_cls E)), ((nb095AlphaDummy293 D R S_cls E),
        (nb095AlphaDummy294 u S_cls f E)), ((nb095AlphaDummy291 D R S_cls E),
        (nb095AlphaDummy292 u S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                                        [((nb095AlphaDummy340 D R S_cls E),
        (nb095AlphaDummy342 u S_cls)), ((nb095AlphaDummy339 D R S_cls E),
        (nb095AlphaDummy341 u S_cls)), ((nb095AlphaDummy337 D R S_cls E),
        (nb095AlphaDummy338 u S_cls E)), ((nb095AlphaDummy335 D R S_cls E),
        (nb095AlphaDummy336 u S_cls E)), ((nb095AlphaDummy293 D R S_cls E),
        (nb095AlphaDummy294 u S_cls f E)), ((nb095AlphaDummy291 D R S_cls E),
        (nb095AlphaDummy292 u S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
                                        (synCcnv (synCdif S_cls (synCid)))
                                        (nb095WppRefl0116 x u D R S_cls f E dv_S_f
        dv_S_u dv_S_x))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed [((nb095AlphaDummy296 D R S_cls E),
                              (nb095AlphaDummy298 f)), ((nb095AlphaDummy295 D R S_cls E),
                              (nb095AlphaDummy297 f)), ((nb095AlphaDummy293 D R S_cls E),
                              (nb095AlphaDummy294 u S_cls f E)),
                            ((nb095AlphaDummy291 D R S_cls E),
                              (nb095AlphaDummy292 u S_cls f E)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)]
                          (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                      (nb095SplitAlpha0030 x u D R S_cls f E)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy295 D R S_cls E) ≠ (nb095AlphaDummy300 D R S_cls E) from (by
          unfold nb095AlphaDummy300;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0324 D
                    R S_cls E)
                  1)))) (show (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy302 f) from (by
          unfold nb095AlphaDummy302;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0326 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy295 D R S_cls E) ≠
        (nb095AlphaDummy299 D R S_cls E) from (by
          unfold nb095AlphaDummy299;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0324
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy301 f) from (by
          unfold nb095AlphaDummy301;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0326
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy295 D R S_cls E) ≠
        (nb095AlphaDummy329 D R S_cls E) from (by
          unfold nb095AlphaDummy329;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0328
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy330 f) from (by
          unfold nb095AlphaDummy330;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0329
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy295 D R S_cls E) ≠
        (nb095AlphaDummy303 D R S_cls E) from (by
          unfold
            nb095AlphaDummy303;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0325
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy304 f) from (by
          unfold
            nb095AlphaDummy304;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0327
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy000
        D R S_cls E))).fv ∪ ((synCvv)).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCvv)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy296 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy295 D R
        S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy298
        f))).fv ∪ ((Class.cv (nb095AlphaDummy297 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb095SplitAlpha0031 x u D R S_cls f
        E))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy295 D R S_cls E) ≠ (nb095AlphaDummy300 D R S_cls E) from (by
          unfold nb095AlphaDummy300;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0324 D
                    R S_cls E)
                  1)))) (show (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy302 f) from (by
          unfold nb095AlphaDummy302;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0326 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy295 D R S_cls E) ≠
        (nb095AlphaDummy299 D R S_cls E) from (by
          unfold nb095AlphaDummy299;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0324
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy301 f) from (by
          unfold nb095AlphaDummy301;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0326
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy295 D R S_cls E) ≠
        (nb095AlphaDummy329 D R S_cls E) from (by
          unfold nb095AlphaDummy329;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0328
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy330 f) from (by
          unfold nb095AlphaDummy330;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0329
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy295 D R S_cls E) ≠
        (nb095AlphaDummy303 D R S_cls E) from (by
          unfold
            nb095AlphaDummy303;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0325
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy304 f) from (by
          unfold
            nb095AlphaDummy304;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0327
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy000
        D R S_cls E))).fv ∪ ((synCvv)).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCvv)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy296 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy295 D R
        S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy298
        f))).fv ∪ ((Class.cv (nb095AlphaDummy297 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb095SplitAlpha0031 x u D R S_cls f
        E)))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy000 D R S_cls E) ≠
                                (nb095AlphaDummy296 D R S_cls E) from (by
                                unfold nb095AlphaDummy296;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0338 D R S_cls E) 1))))
                            (show f ≠ (nb095AlphaDummy298 f) from (by
                                unfold nb095AlphaDummy298;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0339 f) 1))))
                            (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                  (nb095AlphaDummy295 D R S_cls E) from (by
                                  unfold nb095AlphaDummy295;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0338 D R S_cls E) 0))))
                              (show f ≠ (nb095AlphaDummy297 f) from (by
                                  unfold nb095AlphaDummy297;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0339 f) 0))))
                              (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                    (nb095AlphaDummy293 D R S_cls E) from (by
                                    unfold nb095AlphaDummy293;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0336 D R S_cls E) 0))))
                                (show f ≠ (nb095AlphaDummy294 u S_cls f E) from (by
                                    unfold nb095AlphaDummy294;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0337 u S_cls f E) 0))))
                                (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                      (nb095AlphaDummy291 D R S_cls E) from (by
                                      unfold nb095AlphaDummy291;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0334 D R S_cls E) 0))))
                                  (show f ≠ (nb095AlphaDummy292 u S_cls f E) from (by
                                      unfold nb095AlphaDummy292;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0335 u S_cls f E) 0))))
                                  (TAlphaVar.there (freshVar_injective
                                      ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide))
                                    dv_f_u (TAlphaVar.there (freshVar_injective
                                        ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide))
                                      dv_f_x (TAlphaVar.here _ _ _)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfReflOn
                                  [((nb095AlphaDummy337 D R S_cls E),
                                      (nb095AlphaDummy338 u S_cls E)),
                                    ((nb095AlphaDummy335 D R S_cls E),
                                      (nb095AlphaDummy336 u S_cls E)),
                                    ((nb095AlphaDummy293 D R S_cls E),
                                      (nb095AlphaDummy294 u S_cls f E)),
                                    ((nb095AlphaDummy291 D R S_cls E),
                                      (nb095AlphaDummy292 u S_cls f E)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)] E
                                  (nb095FocusedRefl0003 x u D R S_cls f E dv_E_f dv_E_u
                                    dv_E_x)))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy343 D R S_cls E) from (by
          unfold nb095AlphaDummy343;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0350 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy344 u) from (by
          unfold nb095AlphaDummy344;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0351 u)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy340 D R S_cls E) from (by
          unfold nb095AlphaDummy340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R
                    S_cls E)
                  1)))) (show u ≠ (nb095AlphaDummy342 u S_cls) from (by
          unfold nb095AlphaDummy342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0349 u
                    S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy339 D R S_cls E) from (by
          unfold nb095AlphaDummy339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D
                    R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy341 u S_cls) from (by
          unfold nb095AlphaDummy341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0349 u
                    S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy337 D R S_cls E) from (by
          unfold nb095AlphaDummy337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0346
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy338 u S_cls E) from (by
          unfold nb095AlphaDummy338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0347
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy335 D R S_cls E) from (by
          unfold nb095AlphaDummy335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0344
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy336 u S_cls E) from (by
          unfold nb095AlphaDummy336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0345
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy293 D R S_cls E) from (by
          unfold
            nb095AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0342
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy294 u S_cls f E) from (by
          unfold
            nb095AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0343
                    u S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy291 D R S_cls E) from (by
          unfold
            nb095AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0340
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy292 u S_cls f E) from (by
          unfold
            nb095AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0341
                    u S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0032 x u D R S_cls f E))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy339
        D R S_cls E) ≠ (nb095AlphaDummy346 D R S_cls E) from (by
          unfold
            nb095AlphaDummy346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy348 u S_cls)
        from (by
          unfold
            nb095AlphaDummy348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy345 D R S_cls E) from (by
          unfold
            nb095AlphaDummy345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy347 u S_cls)
        from (by
          unfold
            nb095AlphaDummy347;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy375 D R S_cls E) from (by
          unfold
            nb095AlphaDummy375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0384
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy376 u S_cls)
        from (by
          unfold
            nb095AlphaDummy376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0385
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy349 D R S_cls E) from (by
          unfold
            nb095AlphaDummy349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0381
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy350 u S_cls)
        from (by
          unfold
            nb095AlphaDummy350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0383
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif S_cls
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn
        (Class.cv u))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy340
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪ ((Class.cv
        (nb095AlphaDummy341 u S_cls))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (nb095SplitAlpha0033
        x u D R S_cls f E) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb095AlphaDummy377 D R S_cls E),
        (nb095AlphaDummy378 u S_cls)), ((nb095AlphaDummy346 D R S_cls E),
        (nb095AlphaDummy348 u S_cls)), ((nb095AlphaDummy345 D R S_cls E),
        (nb095AlphaDummy347 u S_cls)), ((nb095AlphaDummy375 D R S_cls E),
        (nb095AlphaDummy376 u S_cls)), ((nb095AlphaDummy349 D R S_cls E),
        (nb095AlphaDummy350 u S_cls)), ((nb095AlphaDummy340 D R S_cls E),
        (nb095AlphaDummy342 u S_cls)), ((nb095AlphaDummy339 D R S_cls E),
        (nb095AlphaDummy341 u S_cls)), ((nb095AlphaDummy337 D R S_cls E),
        (nb095AlphaDummy338 u S_cls E)), ((nb095AlphaDummy335 D R S_cls E),
        (nb095AlphaDummy336 u S_cls E)), ((nb095AlphaDummy293 D R S_cls E),
        (nb095AlphaDummy294 u S_cls f E)), ((nb095AlphaDummy291 D R S_cls E),
        (nb095AlphaDummy292 u S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy339
        D R S_cls E) ≠ (nb095AlphaDummy346 D R S_cls E) from (by
          unfold
            nb095AlphaDummy346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy348 u S_cls)
        from (by
          unfold
            nb095AlphaDummy348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy345 D R S_cls E) from (by
          unfold
            nb095AlphaDummy345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy347 u S_cls)
        from (by
          unfold
            nb095AlphaDummy347;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy375 D R S_cls E) from (by
          unfold
            nb095AlphaDummy375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0384
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy376 u S_cls)
        from (by
          unfold
            nb095AlphaDummy376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0385
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy349 D R S_cls E) from (by
          unfold
            nb095AlphaDummy349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0381
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy350 u S_cls)
        from (by
          unfold
            nb095AlphaDummy350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0383
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif S_cls
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn
        (Class.cv u))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy340
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪ ((Class.cv
        (nb095AlphaDummy341 u S_cls))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (nb095SplitAlpha0033
        x u D R S_cls f E) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb095AlphaDummy377 D R S_cls E),
        (nb095AlphaDummy378 u S_cls)), ((nb095AlphaDummy346 D R S_cls E),
        (nb095AlphaDummy348 u S_cls)), ((nb095AlphaDummy345 D R S_cls E),
        (nb095AlphaDummy347 u S_cls)), ((nb095AlphaDummy375 D R S_cls E),
        (nb095AlphaDummy376 u S_cls)), ((nb095AlphaDummy349 D R S_cls E),
        (nb095AlphaDummy350 u S_cls)), ((nb095AlphaDummy340 D R S_cls E),
        (nb095AlphaDummy342 u S_cls)), ((nb095AlphaDummy339 D R S_cls E),
        (nb095AlphaDummy341 u S_cls)), ((nb095AlphaDummy337 D R S_cls E),
        (nb095AlphaDummy338 u S_cls E)), ((nb095AlphaDummy335 D R S_cls E),
        (nb095AlphaDummy336 u S_cls E)), ((nb095AlphaDummy293 D R S_cls E),
        (nb095AlphaDummy294 u S_cls f E)), ((nb095AlphaDummy291 D R S_cls E),
        (nb095AlphaDummy292 u S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
        [((nb095AlphaDummy340 D R S_cls E), (nb095AlphaDummy342 u S_cls)),
        ((nb095AlphaDummy339 D R S_cls E), (nb095AlphaDummy341 u S_cls)),
        ((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcnv (synCdif S_cls (synCid)))
        (nb095WppRefl0116 x u D R S_cls f E dv_S_f dv_S_u dv_S_x)))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfReflOn
                                  [((nb095AlphaDummy337 D R S_cls E),
                                      (nb095AlphaDummy338 u S_cls E)),
                                    ((nb095AlphaDummy335 D R S_cls E),
                                      (nb095AlphaDummy336 u S_cls E)),
                                    ((nb095AlphaDummy293 D R S_cls E),
                                      (nb095AlphaDummy294 u S_cls f E)),
                                    ((nb095AlphaDummy291 D R S_cls E),
                                      (nb095AlphaDummy292 u S_cls f E)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)] E
                                  (nb095FocusedRefl0003 x u D R S_cls f E dv_E_f dv_E_u
                                    dv_E_x)))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy343 D R S_cls E) from (by
          unfold nb095AlphaDummy343;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0350 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy344 u) from (by
          unfold nb095AlphaDummy344;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0351 u)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy340 D R S_cls E) from (by
          unfold nb095AlphaDummy340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R
                    S_cls E)
                  1)))) (show u ≠ (nb095AlphaDummy342 u S_cls) from (by
          unfold nb095AlphaDummy342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0349 u
                    S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy339 D R S_cls E) from (by
          unfold nb095AlphaDummy339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D
                    R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy341 u S_cls) from (by
          unfold nb095AlphaDummy341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0349 u
                    S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy337 D R S_cls E) from (by
          unfold nb095AlphaDummy337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0346
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy338 u S_cls E) from (by
          unfold nb095AlphaDummy338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0347
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy335 D R S_cls E) from (by
          unfold nb095AlphaDummy335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0344
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy336 u S_cls E) from (by
          unfold nb095AlphaDummy336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0345
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy293 D R S_cls E) from (by
          unfold
            nb095AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0342
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy294 u S_cls f E) from (by
          unfold
            nb095AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0343
                    u S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy291 D R S_cls E) from (by
          unfold
            nb095AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0340
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy292 u S_cls f E) from (by
          unfold
            nb095AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0341
                    u S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0032 x u D R S_cls f E))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy339
        D R S_cls E) ≠ (nb095AlphaDummy346 D R S_cls E) from (by
          unfold
            nb095AlphaDummy346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy348 u S_cls)
        from (by
          unfold
            nb095AlphaDummy348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy345 D R S_cls E) from (by
          unfold
            nb095AlphaDummy345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy347 u S_cls)
        from (by
          unfold
            nb095AlphaDummy347;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy375 D R S_cls E) from (by
          unfold
            nb095AlphaDummy375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0384
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy376 u S_cls)
        from (by
          unfold
            nb095AlphaDummy376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0385
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy349 D R S_cls E) from (by
          unfold
            nb095AlphaDummy349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0381
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy350 u S_cls)
        from (by
          unfold
            nb095AlphaDummy350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0383
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif S_cls
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn
        (Class.cv u))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy340
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪ ((Class.cv
        (nb095AlphaDummy341 u S_cls))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (nb095SplitAlpha0033
        x u D R S_cls f E) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb095AlphaDummy377 D R S_cls E),
        (nb095AlphaDummy378 u S_cls)), ((nb095AlphaDummy346 D R S_cls E),
        (nb095AlphaDummy348 u S_cls)), ((nb095AlphaDummy345 D R S_cls E),
        (nb095AlphaDummy347 u S_cls)), ((nb095AlphaDummy375 D R S_cls E),
        (nb095AlphaDummy376 u S_cls)), ((nb095AlphaDummy349 D R S_cls E),
        (nb095AlphaDummy350 u S_cls)), ((nb095AlphaDummy340 D R S_cls E),
        (nb095AlphaDummy342 u S_cls)), ((nb095AlphaDummy339 D R S_cls E),
        (nb095AlphaDummy341 u S_cls)), ((nb095AlphaDummy337 D R S_cls E),
        (nb095AlphaDummy338 u S_cls E)), ((nb095AlphaDummy335 D R S_cls E),
        (nb095AlphaDummy336 u S_cls E)), ((nb095AlphaDummy293 D R S_cls E),
        (nb095AlphaDummy294 u S_cls f E)), ((nb095AlphaDummy291 D R S_cls E),
        (nb095AlphaDummy292 u S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy339
        D R S_cls E) ≠ (nb095AlphaDummy346 D R S_cls E) from (by
          unfold
            nb095AlphaDummy346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy348 u S_cls)
        from (by
          unfold
            nb095AlphaDummy348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy345 D R S_cls E) from (by
          unfold
            nb095AlphaDummy345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy347 u S_cls)
        from (by
          unfold
            nb095AlphaDummy347;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy375 D R S_cls E) from (by
          unfold
            nb095AlphaDummy375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0384
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy376 u S_cls)
        from (by
          unfold
            nb095AlphaDummy376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0385
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy349 D R S_cls E) from (by
          unfold
            nb095AlphaDummy349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0381
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy350 u S_cls)
        from (by
          unfold
            nb095AlphaDummy350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0383
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif S_cls
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn
        (Class.cv u))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy340
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪ ((Class.cv
        (nb095AlphaDummy341 u S_cls))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (nb095SplitAlpha0033
        x u D R S_cls f E) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb095AlphaDummy377 D R S_cls E),
        (nb095AlphaDummy378 u S_cls)), ((nb095AlphaDummy346 D R S_cls E),
        (nb095AlphaDummy348 u S_cls)), ((nb095AlphaDummy345 D R S_cls E),
        (nb095AlphaDummy347 u S_cls)), ((nb095AlphaDummy375 D R S_cls E),
        (nb095AlphaDummy376 u S_cls)), ((nb095AlphaDummy349 D R S_cls E),
        (nb095AlphaDummy350 u S_cls)), ((nb095AlphaDummy340 D R S_cls E),
        (nb095AlphaDummy342 u S_cls)), ((nb095AlphaDummy339 D R S_cls E),
        (nb095AlphaDummy341 u S_cls)), ((nb095AlphaDummy337 D R S_cls E),
        (nb095AlphaDummy338 u S_cls E)), ((nb095AlphaDummy335 D R S_cls E),
        (nb095AlphaDummy336 u S_cls E)), ((nb095AlphaDummy293 D R S_cls E),
        (nb095AlphaDummy294 u S_cls f E)), ((nb095AlphaDummy291 D R S_cls E),
        (nb095AlphaDummy292 u S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
        [((nb095AlphaDummy340 D R S_cls E), (nb095AlphaDummy342 u S_cls)),
        ((nb095AlphaDummy339 D R S_cls E), (nb095AlphaDummy341 u S_cls)),
        ((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcnv (synCdif S_cls (synCid)))
        (nb095WppRefl0116 x u D R S_cls f E dv_S_f dv_S_u dv_S_x)))))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0035`. -/
@[expose]
noncomputable def nb095SplitAlpha0035 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy300 D R S_cls E), (nb095AlphaDummy302 f)),
        ((nb095AlphaDummy299 D R S_cls E), (nb095AlphaDummy301 f)),
        ((nb095AlphaDummy329 D R S_cls E), (nb095AlphaDummy330 f)),
        ((nb095AlphaDummy303 D R S_cls E), (nb095AlphaDummy304 f)),
        ((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
        ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy300 D R S_cls E))
          (Class.cv (nb095AlphaDummy295 D R S_cls E))) (Wff.neg
          (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
            (synCun (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))
              (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy302 f))
          (Class.cv (nb095AlphaDummy297 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
            (synCun (synCphi (Class.cv (nb095AlphaDummy302 f))) (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there
          (show (nb095AlphaDummy295 D R S_cls E) ≠ (nb095AlphaDummy300 D R S_cls E) from
            (by
              unfold nb095AlphaDummy300;
              with_reducible
                exact
                  (Nat.ne_of_lt
                    (mem_lt_freshVar (nb095_support_mem_0324 D R S_cls E) 1))))
          (show (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy302 f) from (by
              unfold nb095AlphaDummy302;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0326 f) 1))))
          (TAlphaVar.there (show
              (nb095AlphaDummy295 D R S_cls E) ≠ (nb095AlphaDummy299 D R S_cls E) from (by
                unfold nb095AlphaDummy299;
                with_reducible
                  exact
                    (Nat.ne_of_lt
                      (mem_lt_freshVar (nb095_support_mem_0324 D R S_cls E) 0))))
            (show (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy301 f) from (by
                unfold nb095AlphaDummy301;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0326 f) 0))))
            (TAlphaVar.there (show
                (nb095AlphaDummy295 D R S_cls E) ≠ (nb095AlphaDummy329 D R S_cls E) from
                (by
                  unfold nb095AlphaDummy329;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb095_support_mem_0328 D R S_cls E) 0))))
              (show (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy330 f) from (by
                  unfold nb095AlphaDummy330;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0329 f) 0))))
              (TAlphaVar.there (show (nb095AlphaDummy295 D R S_cls E) ≠
                    (nb095AlphaDummy303 D R S_cls E) from (by
                    unfold nb095AlphaDummy303;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb095_support_mem_0325 D R S_cls E) 0))))
                (show (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy304 f) from (by
                    unfold nb095AlphaDummy304;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0327 f) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCvv)).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv f)).fv ∪ ((synCvv)).fv) (by decide))
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb095AlphaDummy296 D R S_cls E))).fv ∪
                ((Class.cv (nb095AlphaDummy295 D R S_cls E))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb095AlphaDummy298 f))).fv ∪
                ((Class.cv (nb095AlphaDummy297 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy300 D R S_cls E) ≠
                                        (nb095AlphaDummy307 D R S_cls E) from (by
                                        unfold nb095AlphaDummy307;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0302 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy309 f) from
                                      (by
                                        unfold nb095AlphaDummy309;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0303 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy300 D R S_cls E) ≠
        (nb095AlphaDummy308 D R S_cls E) from (by
                                          unfold nb095AlphaDummy308;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0302 D R S_cls E)
                                                  1)))) (show (nb095AlphaDummy302 f) ≠
        (nb095AlphaDummy310 f) from (by
                                          unfold nb095AlphaDummy310;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0303 f) 1))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy300 D R S_cls E) ≠ (nb095AlphaDummy333 D R S_cls E) from (by
          unfold nb095AlphaDummy333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0332 D R S_cls E)
                  0)))) (show (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy334 f) from (by
          unfold nb095AlphaDummy334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0333 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy300 D R S_cls E) ≠ (nb095AlphaDummy331 D R S_cls E) from (by
          unfold nb095AlphaDummy331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0330 D R S_cls E)
                  0)))) (show (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy332 f) from (by
          unfold nb095AlphaDummy332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0331 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective (((Class.cv
        (nb095AlphaDummy300 D R S_cls E))).fv) (by decide)) (freshVar_injective
                                      (((Class.cv (nb095AlphaDummy302 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy314 D R S_cls E) from (by
          unfold nb095AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy317 f) from (by
          unfold nb095AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307
                    f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy313 D R S_cls E) from (by
          unfold nb095AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy316 f) from (by
          unfold nb095AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy311 D R S_cls E) from (by
          unfold
            nb095AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0304
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from (by
          unfold
            nb095AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0305
                    f)
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
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠
        (nb095AlphaDummy321 D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D
                    R
                    S_cls
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
                    D
                    R
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
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy315
        D R S_cls E) ≠ (nb095AlphaDummy321 D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D
                    R
                    S_cls
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
                    D
                    R
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
        (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠ (nb095AlphaDummy321 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D
                    R
                    S_cls
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
                    D
                    R
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
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy315
        D R S_cls E) ≠ (nb095AlphaDummy321 D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D
                    R
                    S_cls
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
                    D
                    R
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
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy307 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠ (nb095AlphaDummy325 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D
                    R
                    S_cls
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
                    D
                    R
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
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy314
        D R S_cls E) ≠ (nb095AlphaDummy325 D R S_cls E) from (by
          unfold
            nb095AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D
                    R
                    S_cls
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
                    D
                    R
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
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠ (nb095AlphaDummy327 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0322
                    D
                    R
                    S_cls
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
                    D
                    R
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
                    D
                    R
                    S_cls
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
                    D
                    R
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
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy307 D R S_cls E) ≠
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
                  (nb095_support_mem_0305 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb095AlphaDummy311 D R S_cls E),
        (nb095AlphaDummy312 f)), ((nb095AlphaDummy307 D R S_cls E),
        (nb095AlphaDummy309 f)), ((nb095AlphaDummy308 D R S_cls E),
        (nb095AlphaDummy310 f)), ((nb095AlphaDummy333 D R S_cls E),
        (nb095AlphaDummy334 f)), ((nb095AlphaDummy331 D R S_cls E),
        (nb095AlphaDummy332 f)), ((nb095AlphaDummy300 D R S_cls E),
        (nb095AlphaDummy302 f)), ((nb095AlphaDummy299 D R S_cls E),
        (nb095AlphaDummy301 f)), ((nb095AlphaDummy329 D R S_cls E),
        (nb095AlphaDummy330 f)), ((nb095AlphaDummy303 D R S_cls E),
        (nb095AlphaDummy304 f)), ((nb095AlphaDummy296 D R S_cls E),
        (nb095AlphaDummy298 f)), ((nb095AlphaDummy295 D R S_cls E),
        (nb095AlphaDummy297 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy311 D R S_cls E) from (by
          unfold nb095AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0304 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from (by
          unfold nb095AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0305 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb095AlphaDummy307 D R S_cls E) ≠ (nb095AlphaDummy311 D R S_cls E) from (by
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
                  (nb095_support_mem_0305 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb095AlphaDummy311 D R S_cls E),
        (nb095AlphaDummy312 f)), ((nb095AlphaDummy307 D R S_cls E),
        (nb095AlphaDummy309 f)), ((nb095AlphaDummy308 D R S_cls E),
        (nb095AlphaDummy310 f)), ((nb095AlphaDummy333 D R S_cls E),
        (nb095AlphaDummy334 f)), ((nb095AlphaDummy331 D R S_cls E),
        (nb095AlphaDummy332 f)), ((nb095AlphaDummy300 D R S_cls E),
        (nb095AlphaDummy302 f)), ((nb095AlphaDummy299 D R S_cls E),
        (nb095AlphaDummy301 f)), ((nb095AlphaDummy329 D R S_cls E),
        (nb095AlphaDummy330 f)), ((nb095AlphaDummy303 D R S_cls E),
        (nb095AlphaDummy304 f)), ((nb095AlphaDummy296 D R S_cls E),
        (nb095AlphaDummy298 f)), ((nb095AlphaDummy295 D R S_cls E),
        (nb095AlphaDummy297 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy300 D R S_cls E) ≠
                                        (nb095AlphaDummy307 D R S_cls E) from (by
                                        unfold nb095AlphaDummy307;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0302 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy309 f) from
                                      (by
                                        unfold nb095AlphaDummy309;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0303 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy300 D R S_cls E) ≠
        (nb095AlphaDummy308 D R S_cls E) from (by
                                          unfold nb095AlphaDummy308;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0302 D R S_cls E)
                                                  1)))) (show (nb095AlphaDummy302 f) ≠
        (nb095AlphaDummy310 f) from (by
                                          unfold nb095AlphaDummy310;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0303 f) 1))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy300 D R S_cls E) ≠ (nb095AlphaDummy333 D R S_cls E) from (by
          unfold nb095AlphaDummy333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0332 D R S_cls E)
                  0)))) (show (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy334 f) from (by
          unfold nb095AlphaDummy334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0333 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy300 D R S_cls E) ≠ (nb095AlphaDummy331 D R S_cls E) from (by
          unfold nb095AlphaDummy331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0330 D R S_cls E)
                  0)))) (show (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy332 f) from (by
          unfold nb095AlphaDummy332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0331 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective (((Class.cv
        (nb095AlphaDummy300 D R S_cls E))).fv) (by decide)) (freshVar_injective
                                      (((Class.cv (nb095AlphaDummy302 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy314 D R S_cls E) from (by
          unfold nb095AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy317 f) from (by
          unfold nb095AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307
                    f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy313 D R S_cls E) from (by
          unfold nb095AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy316 f) from (by
          unfold nb095AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy311 D R S_cls E) from (by
          unfold
            nb095AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0304
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from (by
          unfold
            nb095AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0305
                    f)
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
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠
        (nb095AlphaDummy321 D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D
                    R
                    S_cls
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
                    D
                    R
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
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy315
        D R S_cls E) ≠ (nb095AlphaDummy321 D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D
                    R
                    S_cls
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
                    D
                    R
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
        (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠ (nb095AlphaDummy321 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D
                    R
                    S_cls
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
                    D
                    R
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
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy315
        D R S_cls E) ≠ (nb095AlphaDummy321 D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D
                    R
                    S_cls
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
                    D
                    R
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
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy307 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠ (nb095AlphaDummy325 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D
                    R
                    S_cls
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
                    D
                    R
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
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy314
        D R S_cls E) ≠ (nb095AlphaDummy325 D R S_cls E) from (by
          unfold
            nb095AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D
                    R
                    S_cls
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
                    D
                    R
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
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠ (nb095AlphaDummy327 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0322
                    D
                    R
                    S_cls
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
                    D
                    R
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
                    D
                    R
                    S_cls
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
                    D
                    R
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
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy307 D R S_cls E) ≠
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
                  (nb095_support_mem_0305 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb095AlphaDummy311 D R S_cls E),
        (nb095AlphaDummy312 f)), ((nb095AlphaDummy307 D R S_cls E),
        (nb095AlphaDummy309 f)), ((nb095AlphaDummy308 D R S_cls E),
        (nb095AlphaDummy310 f)), ((nb095AlphaDummy333 D R S_cls E),
        (nb095AlphaDummy334 f)), ((nb095AlphaDummy331 D R S_cls E),
        (nb095AlphaDummy332 f)), ((nb095AlphaDummy300 D R S_cls E),
        (nb095AlphaDummy302 f)), ((nb095AlphaDummy299 D R S_cls E),
        (nb095AlphaDummy301 f)), ((nb095AlphaDummy329 D R S_cls E),
        (nb095AlphaDummy330 f)), ((nb095AlphaDummy303 D R S_cls E),
        (nb095AlphaDummy304 f)), ((nb095AlphaDummy296 D R S_cls E),
        (nb095AlphaDummy298 f)), ((nb095AlphaDummy295 D R S_cls E),
        (nb095AlphaDummy297 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy311 D R S_cls E) from (by
          unfold nb095AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0304 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from (by
          unfold nb095AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0305 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb095AlphaDummy307 D R S_cls E) ≠ (nb095AlphaDummy311 D R S_cls E) from (by
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
                  (nb095_support_mem_0305 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb095AlphaDummy311 D R S_cls E),
        (nb095AlphaDummy312 f)), ((nb095AlphaDummy307 D R S_cls E),
        (nb095AlphaDummy309 f)), ((nb095AlphaDummy308 D R S_cls E),
        (nb095AlphaDummy310 f)), ((nb095AlphaDummy333 D R S_cls E),
        (nb095AlphaDummy334 f)), ((nb095AlphaDummy331 D R S_cls E),
        (nb095AlphaDummy332 f)), ((nb095AlphaDummy300 D R S_cls E),
        (nb095AlphaDummy302 f)), ((nb095AlphaDummy299 D R S_cls E),
        (nb095AlphaDummy301 f)), ((nb095AlphaDummy329 D R S_cls E),
        (nb095AlphaDummy330 f)), ((nb095AlphaDummy303 D R S_cls E),
        (nb095AlphaDummy304 f)), ((nb095AlphaDummy296 D R S_cls E),
        (nb095AlphaDummy298 f)), ((nb095AlphaDummy295 D R S_cls E),
        (nb095AlphaDummy297 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb095AlphaDummy331 D R S_cls E), (nb095AlphaDummy332 f)),
                    ((nb095AlphaDummy300 D R S_cls E), (nb095AlphaDummy302 f)),
                    ((nb095AlphaDummy299 D R S_cls E), (nb095AlphaDummy301 f)),
                    ((nb095AlphaDummy329 D R S_cls E), (nb095AlphaDummy330 f)),
                    ((nb095AlphaDummy303 D R S_cls E), (nb095AlphaDummy304 f)),
                    ((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
                    ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
                    ((nb095AlphaDummy001 D R S_cls E), u),
                    ((nb095AlphaDummy002 D R S_cls E), x),
                    ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0036`. -/
@[expose]
noncomputable def nb095SplitAlpha0036 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy303 D R S_cls E), (nb095AlphaDummy304 f)),
        ((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
        ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy303 D R S_cls E)) (synCcompl
            (Class.cab (nb095AlphaDummy299 D R S_cls E)
              (synWrex (nb095AlphaDummy300 D R S_cls E)
                (Class.cv (nb095AlphaDummy296 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy303 D R S_cls E)) (synCcompl
              (Class.cab (nb095AlphaDummy299 D R S_cls E)
                (synWrex (nb095AlphaDummy300 D R S_cls E)
                  (Class.cv (nb095AlphaDummy295 D R S_cls E))
                  (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
                    (synCun (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy304 f)) (synCcompl
            (Class.cab (nb095AlphaDummy301 f)
              (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy298 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
                  (synCphi (Class.cv (nb095AlphaDummy302 f)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy304 f)) (synCcompl
              (Class.cab (nb095AlphaDummy301 f)
                (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy297 f))
                  (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
                    (synCun (synCphi (Class.cv (nb095AlphaDummy302 f)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy296 D R S_cls E) ≠
                              (nb095AlphaDummy300 D R S_cls E) from (by
                              unfold nb095AlphaDummy300;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0296 D R S_cls E)
                                      1))))
                          (show (nb095AlphaDummy298 f) ≠ (nb095AlphaDummy302 f) from (by
                              unfold nb095AlphaDummy302;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0298 f) 1))))
                          (TAlphaVar.there (show (nb095AlphaDummy296 D R S_cls E) ≠
                                (nb095AlphaDummy299 D R S_cls E) from (by
                                unfold nb095AlphaDummy299;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0296 D R S_cls E) 0))))
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
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0300 D R S_cls E) 0))))
                              (show (nb095AlphaDummy298 f) ≠ (nb095AlphaDummy306 f) from
                                (by
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
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0297 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy298 f) ≠ (nb095AlphaDummy304 f) from (by
                                    unfold nb095AlphaDummy304;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0299 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy296 D R S_cls E))).fv ∪
                              ((Class.cv (nb095AlphaDummy295 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy298 f))).fv ∪
                              ((Class.cv (nb095AlphaDummy297 f))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy300 D R S_cls E) ≠
                                      (nb095AlphaDummy307 D R S_cls E) from (by
                                      unfold nb095AlphaDummy307;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0302 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy309 f) from
                                    (by
                                      unfold nb095AlphaDummy309;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0303 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy300 D R S_cls E) ≠
                                        (nb095AlphaDummy308 D R S_cls E) from (by
                                        unfold nb095AlphaDummy308;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0302 D R S_cls E) 1)))) (show
                                      (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy310 f) from
                                      (by
                                        unfold nb095AlphaDummy310;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0303 f)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb095AlphaDummy300 D R S_cls E))).fv)
                                    (by decide)) (freshVar_injective
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
                  (nb095_support_mem_0306 D
                    R S_cls E)
                  1)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy317 f) from (by
          unfold nb095AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy313 D R S_cls E) from (by
          unfold nb095AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy316 f) from (by
          unfold nb095AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy311 D R S_cls E) from (by
          unfold nb095AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0304
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from (by
          unfold nb095AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0305
                    f)
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
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠
        (nb095AlphaDummy321 D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D
                    R
                    S_cls
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
                    D
                    R
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
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy315
        D R S_cls E) ≠ (nb095AlphaDummy321 D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D
                    R
                    S_cls
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
                    D
                    R
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
                    D
                    R
                    S_cls
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
                    D
                    R
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
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy315
        D R S_cls E) ≠ (nb095AlphaDummy321 D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D
                    R
                    S_cls
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
                    D
                    R
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
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy307 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
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
                    D
                    R
                    S_cls
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
                    D
                    R
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
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy314
        D R S_cls E) ≠ (nb095AlphaDummy325 D R S_cls E) from (by
          unfold
            nb095AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D
                    R
                    S_cls
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
                    D
                    R
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
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠ (nb095AlphaDummy327
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0322
                    D
                    R
                    S_cls
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
                    D
                    R
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
                    D
                    R
                    S_cls
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
                    D
                    R
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
        (nb095AlphaDummy307 D R S_cls E) ≠ (nb095AlphaDummy311 D R S_cls E) from (by
          unfold nb095AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0304 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from (by
          unfold nb095AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0305 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy311 D R S_cls E), (nb095AlphaDummy312 f)),
        ((nb095AlphaDummy307 D R S_cls E), (nb095AlphaDummy309 f)),
        ((nb095AlphaDummy308 D R S_cls E), (nb095AlphaDummy310 f)),
        ((nb095AlphaDummy300 D R S_cls E), (nb095AlphaDummy302 f)),
        ((nb095AlphaDummy299 D R S_cls E), (nb095AlphaDummy301 f)),
        ((nb095AlphaDummy305 D R S_cls E), (nb095AlphaDummy306 f)),
        ((nb095AlphaDummy303 D R S_cls E), (nb095AlphaDummy304 f)),
        ((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
        ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095AlphaDummy307 D R S_cls E) ≠ (nb095AlphaDummy311 D R S_cls E) from (by
          unfold nb095AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0304 D R S_cls E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from (by
          unfold nb095AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0305 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy307 D R S_cls E) ≠ (nb095AlphaDummy311 D R S_cls E) from (by
          unfold nb095AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0304 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from (by
          unfold nb095AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0305 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy311 D R S_cls E), (nb095AlphaDummy312 f)),
        ((nb095AlphaDummy307 D R S_cls E), (nb095AlphaDummy309 f)),
        ((nb095AlphaDummy308 D R S_cls E), (nb095AlphaDummy310 f)),
        ((nb095AlphaDummy300 D R S_cls E), (nb095AlphaDummy302 f)),
        ((nb095AlphaDummy299 D R S_cls E), (nb095AlphaDummy301 f)),
        ((nb095AlphaDummy305 D R S_cls E), (nb095AlphaDummy306 f)),
        ((nb095AlphaDummy303 D R S_cls E), (nb095AlphaDummy304 f)),
        ((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
        ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy296 D R S_cls E) ≠
                              (nb095AlphaDummy300 D R S_cls E) from (by
                              unfold nb095AlphaDummy300;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0296 D R S_cls E)
                                      1))))
                          (show (nb095AlphaDummy298 f) ≠ (nb095AlphaDummy302 f) from (by
                              unfold nb095AlphaDummy302;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0298 f) 1))))
                          (TAlphaVar.there (show (nb095AlphaDummy296 D R S_cls E) ≠
                                (nb095AlphaDummy299 D R S_cls E) from (by
                                unfold nb095AlphaDummy299;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0296 D R S_cls E) 0))))
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
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0300 D R S_cls E) 0))))
                              (show (nb095AlphaDummy298 f) ≠ (nb095AlphaDummy306 f) from
                                (by
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
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0297 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy298 f) ≠ (nb095AlphaDummy304 f) from (by
                                    unfold nb095AlphaDummy304;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0299 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy296 D R S_cls E))).fv ∪
                              ((Class.cv (nb095AlphaDummy295 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy298 f))).fv ∪
                              ((Class.cv (nb095AlphaDummy297 f))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy300 D R S_cls E) ≠
                                      (nb095AlphaDummy307 D R S_cls E) from (by
                                      unfold nb095AlphaDummy307;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0302 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy309 f) from
                                    (by
                                      unfold nb095AlphaDummy309;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0303 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy300 D R S_cls E) ≠
                                        (nb095AlphaDummy308 D R S_cls E) from (by
                                        unfold nb095AlphaDummy308;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0302 D R S_cls E) 1)))) (show
                                      (nb095AlphaDummy302 f) ≠ (nb095AlphaDummy310 f) from
                                      (by
                                        unfold nb095AlphaDummy310;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0303 f)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb095AlphaDummy300 D R S_cls E))).fv)
                                    (by decide)) (freshVar_injective
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
                  (nb095_support_mem_0306 D
                    R S_cls E)
                  1)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy317 f) from (by
          unfold nb095AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy313 D R S_cls E) from (by
          unfold nb095AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy316 f) from (by
          unfold nb095AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy307 D R S_cls E) ≠
        (nb095AlphaDummy311 D R S_cls E) from (by
          unfold nb095AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0304
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from (by
          unfold nb095AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0305
                    f)
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
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy314 D R S_cls E) ≠
        (nb095AlphaDummy321 D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D
                    R
                    S_cls
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
                    D
                    R
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
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy315
        D R S_cls E) ≠ (nb095AlphaDummy321 D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D
                    R
                    S_cls
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
                    D
                    R
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
                    D
                    R
                    S_cls
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
                    D
                    R
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
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy315
        D R S_cls E) ≠ (nb095AlphaDummy321 D R S_cls E) from (by
          unfold
            nb095AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D
                    R
                    S_cls
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
                    D
                    R
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
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy307 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy307
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
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
                    D
                    R
                    S_cls
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
                    D
                    R
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
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy314
        D R S_cls E) ≠ (nb095AlphaDummy325 D R S_cls E) from (by
          unfold
            nb095AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D
                    R
                    S_cls
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
                    D
                    R
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
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy315 D R S_cls E) ≠ (nb095AlphaDummy327
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0322
                    D
                    R
                    S_cls
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
                    D
                    R
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
                    D
                    R
                    S_cls
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
                    D
                    R
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
        (nb095AlphaDummy307 D R S_cls E) ≠ (nb095AlphaDummy311 D R S_cls E) from (by
          unfold nb095AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0304 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from (by
          unfold nb095AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0305 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy311 D R S_cls E), (nb095AlphaDummy312 f)),
        ((nb095AlphaDummy307 D R S_cls E), (nb095AlphaDummy309 f)),
        ((nb095AlphaDummy308 D R S_cls E), (nb095AlphaDummy310 f)),
        ((nb095AlphaDummy300 D R S_cls E), (nb095AlphaDummy302 f)),
        ((nb095AlphaDummy299 D R S_cls E), (nb095AlphaDummy301 f)),
        ((nb095AlphaDummy305 D R S_cls E), (nb095AlphaDummy306 f)),
        ((nb095AlphaDummy303 D R S_cls E), (nb095AlphaDummy304 f)),
        ((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
        ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095AlphaDummy307 D R S_cls E) ≠ (nb095AlphaDummy311 D R S_cls E) from (by
          unfold nb095AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0304 D R S_cls E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from (by
          unfold nb095AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0305 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy307 D R S_cls E) ≠ (nb095AlphaDummy311 D R S_cls E) from (by
          unfold nb095AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0304 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy312 f) from (by
          unfold nb095AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0305 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy311 D R S_cls E), (nb095AlphaDummy312 f)),
        ((nb095AlphaDummy307 D R S_cls E), (nb095AlphaDummy309 f)),
        ((nb095AlphaDummy308 D R S_cls E), (nb095AlphaDummy310 f)),
        ((nb095AlphaDummy300 D R S_cls E), (nb095AlphaDummy302 f)),
        ((nb095AlphaDummy299 D R S_cls E), (nb095AlphaDummy301 f)),
        ((nb095AlphaDummy305 D R S_cls E), (nb095AlphaDummy306 f)),
        ((nb095AlphaDummy303 D R S_cls E), (nb095AlphaDummy304 f)),
        ((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
        ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb095SplitAlpha0035 x u D R S_cls f E)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex
                    (TAlphaWff.neg (nb095SplitAlpha0035 x u D R S_cls f E)))))))))))

theorem nb095_compact_fv_empty_0312 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy383 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0313 (f : Var) :
    (nb095AlphaDummy384 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0314 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy381 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0315 (f : Var) :
    (nb095AlphaDummy382 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
