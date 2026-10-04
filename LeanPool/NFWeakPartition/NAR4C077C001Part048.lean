/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C077C001Block016

/-! NF weak partition development: NAR4C077C001Part048. -/


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

/-- Checked nominal proof certificate identified upstream as `nb077_split_alpha_0034`. -/
@[expose]
noncomputable def nb077SplitAlpha0034 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077AlphaDummy345 F I), (nb077AlphaDummy346 x)),
        ((nb077AlphaDummy343 F I), (nb077AlphaDummy344 x)),
        ((nb077AlphaDummy312 F I), (nb077AlphaDummy314 x)),
        ((nb077AlphaDummy311 F I), (nb077AlphaDummy313 x)),
        ((nb077AlphaDummy341 F I), (nb077AlphaDummy342 x)),
        ((nb077AlphaDummy315 F I), (nb077AlphaDummy316 x)),
        ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy345 F I))
          (synCphi (Class.cv (nb077AlphaDummy312 F I)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy345 F I))
            (synCphi (Class.cv (nb077AlphaDummy312 F I))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy346 x))
          (synCphi (Class.cv (nb077AlphaDummy314 x)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy346 x))
            (synCphi (Class.cv (nb077AlphaDummy314 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077AlphaDummy312 F I) ≠ (nb077AlphaDummy319 F I) from (by
                      unfold nb077AlphaDummy319;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0314 F I) 0))))
                  (show (nb077AlphaDummy314 x) ≠ (nb077AlphaDummy321 x) from (by
                      unfold nb077AlphaDummy321;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0315 x) 0))))
                  (TAlphaVar.there
                    (show (nb077AlphaDummy312 F I) ≠ (nb077AlphaDummy320 F I) from (by
                        unfold nb077AlphaDummy320;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0314 F I) 1))))
                    (show (nb077AlphaDummy314 x) ≠ (nb077AlphaDummy322 x) from (by
                        unfold nb077AlphaDummy322;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0315 x) 1)))) (TAlphaVar.there
                      (show (nb077AlphaDummy312 F I) ≠ (nb077AlphaDummy345 F I) from (by
                          unfold nb077AlphaDummy345;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0344 F I) 0))))
                      (show (nb077AlphaDummy314 x) ≠ (nb077AlphaDummy346 x) from (by
                          unfold nb077AlphaDummy346;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0345 x) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy312 F I) ≠ (nb077AlphaDummy343 F I) from (by
                            unfold nb077AlphaDummy343;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0342 F I) 0))))
                        (show (nb077AlphaDummy314 x) ≠ (nb077AlphaDummy344 x) from (by
                            unfold nb077AlphaDummy344;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0343 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb077AlphaDummy312 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077AlphaDummy314 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy319 F I) ≠ (nb077AlphaDummy326 F I)
                                      from (by
                                        unfold nb077AlphaDummy326;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0318 F I) 1)))) (show
                                      (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy329 x) from
                                      (by
                                        unfold nb077AlphaDummy329;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0319 x)
                                                1)))) (TAlphaVar.there (show
                                        (nb077AlphaDummy319 F I) ≠
        (nb077AlphaDummy325 F I) from (by
                                          unfold nb077AlphaDummy325;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0318 F I) 0)))) (show
                                        (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy328 x)
                                        from (by
                                          unfold nb077AlphaDummy328;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0319 x) 0))))
                                      (TAlphaVar.there (show (nb077AlphaDummy319 F I) ≠
        (nb077AlphaDummy323 F I) from (by
          unfold nb077AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0316 F I) 0)))) (show (nb077AlphaDummy321 x) ≠
        (nb077AlphaDummy324 x) from (by
          unfold nb077AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0317 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb077AlphaDummy327 F I),
        (nb077AlphaDummy330 x)), ((nb077AlphaDummy326 F I), (nb077AlphaDummy329 x)),
                                        ((nb077AlphaDummy325 F I),
        (nb077AlphaDummy328 x)), ((nb077AlphaDummy323 F I), (nb077AlphaDummy324 x)),
                                        ((nb077AlphaDummy319 F I),
        (nb077AlphaDummy321 x)), ((nb077AlphaDummy320 F I), (nb077AlphaDummy322 x)),
                                        ((nb077AlphaDummy345 F I),
        (nb077AlphaDummy346 x)), ((nb077AlphaDummy343 F I), (nb077AlphaDummy344 x)),
                                        ((nb077AlphaDummy312 F I),
        (nb077AlphaDummy314 x)), ((nb077AlphaDummy311 F I), (nb077AlphaDummy313 x)),
                                        ((nb077AlphaDummy341 F I),
        (nb077AlphaDummy342 x)), ((nb077AlphaDummy315 F I), (nb077AlphaDummy316 x)),
                                        ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                                        ((nb077AlphaDummy059 F I),
        (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                                        ((nb077AlphaDummy057 F I),
        (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F I),
        (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I),
        (nb077AlphaDummy018 x F I)), ((nb077AlphaDummy015 F I),
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy001 F I),
        (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy326 F I) ≠ (nb077AlphaDummy333 F I) from (by
          unfold
            nb077AlphaDummy333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0322
                    F I)
                  0)))) (show (nb077AlphaDummy329 x) ≠ (nb077AlphaDummy334 x) from (by
          unfold
            nb077AlphaDummy334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0323
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy326 F I) ≠
        (nb077AlphaDummy331 F I) from (by
          unfold
            nb077AlphaDummy331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0320
                    F I)
                  0)))) (show (nb077AlphaDummy329 x) ≠ (nb077AlphaDummy332 x) from (by
          unfold
            nb077AlphaDummy332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0321
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy319
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy327 F I) ≠
        (nb077AlphaDummy333 F I) from (by
          unfold
            nb077AlphaDummy333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0326
                    F I)
                  0)))) (show (nb077AlphaDummy330 x) ≠ (nb077AlphaDummy334 x) from (by
          unfold
            nb077AlphaDummy334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0327
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy327 F I) ≠
        (nb077AlphaDummy331 F I) from (by
          unfold
            nb077AlphaDummy331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0324
                    F I)
                  0)))) (show (nb077AlphaDummy330 x) ≠ (nb077AlphaDummy332 x) from (by
          unfold
            nb077AlphaDummy332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0325
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy326 F I) ≠ (nb077AlphaDummy333 F I) from
        (by
          unfold
            nb077AlphaDummy333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0322
                    F I)
                  0)))) (show (nb077AlphaDummy329 x) ≠ (nb077AlphaDummy334 x) from (by
          unfold
            nb077AlphaDummy334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0323
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy326 F I) ≠
        (nb077AlphaDummy331 F I) from (by
          unfold
            nb077AlphaDummy331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0320
                    F I)
                  0)))) (show (nb077AlphaDummy329 x) ≠ (nb077AlphaDummy332 x) from (by
          unfold
            nb077AlphaDummy332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0321
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy319
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy327 F I) ≠
        (nb077AlphaDummy333 F I) from (by
          unfold
            nb077AlphaDummy333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0326
                    F I)
                  0)))) (show (nb077AlphaDummy330 x) ≠ (nb077AlphaDummy334 x) from (by
          unfold
            nb077AlphaDummy334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0327
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy327 F I) ≠
        (nb077AlphaDummy331 F I) from (by
          unfold
            nb077AlphaDummy331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0324
                    F I)
                  0)))) (show (nb077AlphaDummy330 x) ≠ (nb077AlphaDummy332 x) from (by
          unfold
            nb077AlphaDummy332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0325
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb077AlphaDummy327 F I),
        (nb077AlphaDummy330 x)), ((nb077AlphaDummy326 F I), (nb077AlphaDummy329 x)),
        ((nb077AlphaDummy325 F I), (nb077AlphaDummy328 x)), ((nb077AlphaDummy323 F I),
        (nb077AlphaDummy324 x)), ((nb077AlphaDummy319 F I), (nb077AlphaDummy321 x)),
        ((nb077AlphaDummy320 F I), (nb077AlphaDummy322 x)), ((nb077AlphaDummy345 F I),
        (nb077AlphaDummy346 x)), ((nb077AlphaDummy343 F I), (nb077AlphaDummy344 x)),
        ((nb077AlphaDummy312 F I), (nb077AlphaDummy314 x)), ((nb077AlphaDummy311 F I),
        (nb077AlphaDummy313 x)), ((nb077AlphaDummy341 F I), (nb077AlphaDummy342 x)),
        ((nb077AlphaDummy315 F I), (nb077AlphaDummy316 x)), ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077AlphaDummy319 F I))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy319 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy326 F I) ≠ (nb077AlphaDummy337 F I) from (by
          unfold
            nb077AlphaDummy337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0330
                    F I)
                  0)))) (show (nb077AlphaDummy329 x) ≠ (nb077AlphaDummy338 x) from (by
          unfold
            nb077AlphaDummy338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0331
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy326 F I) ≠
        (nb077AlphaDummy335 F I) from (by
          unfold
            nb077AlphaDummy335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0328
                    F I)
                  0)))) (show (nb077AlphaDummy329 x) ≠ (nb077AlphaDummy336 x) from (by
          unfold
            nb077AlphaDummy336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0329
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy319
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy326 F I) ≠
        (nb077AlphaDummy337 F I) from (by
          unfold
            nb077AlphaDummy337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0330
                    F I)
                  0)))) (show (nb077AlphaDummy329 x) ≠ (nb077AlphaDummy338 x) from (by
          unfold
            nb077AlphaDummy338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0331
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy326 F I) ≠
        (nb077AlphaDummy335 F I) from (by
          unfold
            nb077AlphaDummy335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0328
                    F I)
                  0)))) (show (nb077AlphaDummy329 x) ≠ (nb077AlphaDummy336 x) from (by
          unfold
            nb077AlphaDummy336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0329
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy319
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy327 F I) ≠ (nb077AlphaDummy339 F I) from (by
          unfold
            nb077AlphaDummy339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0334
                    F I)
                  0)))) (show (nb077AlphaDummy330 x) ≠ (nb077AlphaDummy340 x) from (by
          unfold
            nb077AlphaDummy340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0335
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy327 F I) ≠
        (nb077AlphaDummy335 F I) from (by
          unfold
            nb077AlphaDummy335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0332
                    F I)
                  0)))) (show (nb077AlphaDummy330 x) ≠ (nb077AlphaDummy336 x) from (by
          unfold
            nb077AlphaDummy336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0333
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy327 F I) ≠ (nb077AlphaDummy339 F I) from (by
          unfold
            nb077AlphaDummy339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0334
                    F I)
                  0)))) (show (nb077AlphaDummy330 x) ≠ (nb077AlphaDummy340 x) from (by
          unfold
            nb077AlphaDummy340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0335
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy327 F I) ≠
        (nb077AlphaDummy335 F I) from (by
          unfold
            nb077AlphaDummy335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0332
                    F I)
                  0)))) (show (nb077AlphaDummy330 x) ≠ (nb077AlphaDummy336 x) from (by
          unfold
            nb077AlphaDummy336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0333
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy319 F I) ≠ (nb077AlphaDummy323 F I) from (by
                                unfold nb077AlphaDummy323;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0316 F I) 0))))
                            (show (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy324 x) from (by
                                unfold nb077AlphaDummy324;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0317 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb077AlphaDummy323 F I), (nb077AlphaDummy324 x)),
                            ((nb077AlphaDummy319 F I), (nb077AlphaDummy321 x)),
                            ((nb077AlphaDummy320 F I), (nb077AlphaDummy322 x)),
                            ((nb077AlphaDummy345 F I), (nb077AlphaDummy346 x)),
                            ((nb077AlphaDummy343 F I), (nb077AlphaDummy344 x)),
                            ((nb077AlphaDummy312 F I), (nb077AlphaDummy314 x)),
                            ((nb077AlphaDummy311 F I), (nb077AlphaDummy313 x)),
                            ((nb077AlphaDummy341 F I), (nb077AlphaDummy342 x)),
                            ((nb077AlphaDummy315 F I), (nb077AlphaDummy316 x)),
                            ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                            ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                            ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                            ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                            ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                            ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                            ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
                            ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
                            ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                            ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                            ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077AlphaDummy319 F I) ≠ (nb077AlphaDummy323 F I) from
                            (by
                              unfold nb077AlphaDummy323;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0316 F I) 0))))
                          (show (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy324 x) from (by
                              unfold nb077AlphaDummy324;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0317 x) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy319 F I) ≠ (nb077AlphaDummy323 F I) from (by
                                unfold nb077AlphaDummy323;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0316 F I) 0))))
                            (show (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy324 x) from (by
                                unfold nb077AlphaDummy324;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0317 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb077AlphaDummy323 F I), (nb077AlphaDummy324 x)),
                            ((nb077AlphaDummy319 F I), (nb077AlphaDummy321 x)),
                            ((nb077AlphaDummy320 F I), (nb077AlphaDummy322 x)),
                            ((nb077AlphaDummy345 F I), (nb077AlphaDummy346 x)),
                            ((nb077AlphaDummy343 F I), (nb077AlphaDummy344 x)),
                            ((nb077AlphaDummy312 F I), (nb077AlphaDummy314 x)),
                            ((nb077AlphaDummy311 F I), (nb077AlphaDummy313 x)),
                            ((nb077AlphaDummy341 F I), (nb077AlphaDummy342 x)),
                            ((nb077AlphaDummy315 F I), (nb077AlphaDummy316 x)),
                            ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                            ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                            ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                            ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                            ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                            ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                            ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
                            ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
                            ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                            ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                            ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb077AlphaDummy312 F I) ≠ (nb077AlphaDummy319 F I) from (by
                        unfold nb077AlphaDummy319;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0314 F I) 0))))
                    (show (nb077AlphaDummy314 x) ≠ (nb077AlphaDummy321 x) from (by
                        unfold nb077AlphaDummy321;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0315 x) 0)))) (TAlphaVar.there
                      (show (nb077AlphaDummy312 F I) ≠ (nb077AlphaDummy320 F I) from (by
                          unfold nb077AlphaDummy320;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0314 F I) 1))))
                      (show (nb077AlphaDummy314 x) ≠ (nb077AlphaDummy322 x) from (by
                          unfold nb077AlphaDummy322;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0315 x) 1))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy312 F I) ≠ (nb077AlphaDummy345 F I) from (by
                            unfold nb077AlphaDummy345;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0344 F I) 0))))
                        (show (nb077AlphaDummy314 x) ≠ (nb077AlphaDummy346 x) from (by
                            unfold nb077AlphaDummy346;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0345 x) 0))))
                        (TAlphaVar.there
                          (show (nb077AlphaDummy312 F I) ≠ (nb077AlphaDummy343 F I) from
                            (by
                              unfold nb077AlphaDummy343;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0342 F I) 0))))
                          (show (nb077AlphaDummy314 x) ≠ (nb077AlphaDummy344 x) from (by
                              unfold nb077AlphaDummy344;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0343 x) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb077AlphaDummy312 F I))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb077AlphaDummy314 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb077AlphaDummy319 F I) ≠
        (nb077AlphaDummy326 F I) from (by
                                          unfold nb077AlphaDummy326;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0318 F I) 1)))) (show
                                        (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy329 x)
                                        from (by
                                          unfold nb077AlphaDummy329;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0319 x) 1))))
                                      (TAlphaVar.there (show (nb077AlphaDummy319 F I) ≠
        (nb077AlphaDummy325 F I) from (by
          unfold nb077AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0318 F I) 0)))) (show (nb077AlphaDummy321 x) ≠
        (nb077AlphaDummy328 x) from (by
          unfold nb077AlphaDummy328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0319 x) 0)))) (TAlphaVar.there (show
        (nb077AlphaDummy319 F I) ≠ (nb077AlphaDummy323 F I) from (by
          unfold nb077AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0316 F I) 0)))) (show (nb077AlphaDummy321 x) ≠
        (nb077AlphaDummy324 x) from (by
          unfold nb077AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0317 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb077AlphaDummy327 F I),
        (nb077AlphaDummy330 x)), ((nb077AlphaDummy326 F I), (nb077AlphaDummy329 x)),
        ((nb077AlphaDummy325 F I), (nb077AlphaDummy328 x)), ((nb077AlphaDummy323 F I),
        (nb077AlphaDummy324 x)), ((nb077AlphaDummy319 F I), (nb077AlphaDummy321 x)),
        ((nb077AlphaDummy320 F I), (nb077AlphaDummy322 x)), ((nb077AlphaDummy345 F I),
        (nb077AlphaDummy346 x)), ((nb077AlphaDummy343 F I), (nb077AlphaDummy344 x)),
        ((nb077AlphaDummy312 F I), (nb077AlphaDummy314 x)), ((nb077AlphaDummy311 F I),
        (nb077AlphaDummy313 x)), ((nb077AlphaDummy341 F I), (nb077AlphaDummy342 x)),
        ((nb077AlphaDummy315 F I), (nb077AlphaDummy316 x)), ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy326 F
        I) ≠ (nb077AlphaDummy333 F I) from (by
          unfold
            nb077AlphaDummy333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0322
                    F I)
                  0)))) (show (nb077AlphaDummy329 x) ≠ (nb077AlphaDummy334 x) from (by
          unfold
            nb077AlphaDummy334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0323
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy326 F I) ≠
        (nb077AlphaDummy331 F I) from (by
          unfold
            nb077AlphaDummy331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0320
                    F I)
                  0)))) (show (nb077AlphaDummy329 x) ≠ (nb077AlphaDummy332 x) from (by
          unfold
            nb077AlphaDummy332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0321
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy319
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy327 F I) ≠ (nb077AlphaDummy333 F I) from
        (by
          unfold
            nb077AlphaDummy333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0326
                    F I)
                  0)))) (show (nb077AlphaDummy330 x) ≠ (nb077AlphaDummy334 x) from (by
          unfold
            nb077AlphaDummy334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0327
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy327 F I) ≠
        (nb077AlphaDummy331 F I) from (by
          unfold
            nb077AlphaDummy331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0324
                    F I)
                  0)))) (show (nb077AlphaDummy330 x) ≠ (nb077AlphaDummy332 x) from (by
          unfold
            nb077AlphaDummy332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0325
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy326 F I) ≠ (nb077AlphaDummy333 F I) from
        (by
          unfold
            nb077AlphaDummy333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0322
                    F I)
                  0)))) (show (nb077AlphaDummy329 x) ≠ (nb077AlphaDummy334 x) from (by
          unfold
            nb077AlphaDummy334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0323
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy326 F I) ≠
        (nb077AlphaDummy331 F I) from (by
          unfold
            nb077AlphaDummy331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0320
                    F I)
                  0)))) (show (nb077AlphaDummy329 x) ≠ (nb077AlphaDummy332 x) from (by
          unfold
            nb077AlphaDummy332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0321
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy319
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy327 F I) ≠ (nb077AlphaDummy333 F I) from
        (by
          unfold
            nb077AlphaDummy333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0326
                    F I)
                  0)))) (show (nb077AlphaDummy330 x) ≠ (nb077AlphaDummy334 x) from (by
          unfold
            nb077AlphaDummy334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0327
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy327 F I) ≠
        (nb077AlphaDummy331 F I) from (by
          unfold
            nb077AlphaDummy331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0324
                    F I)
                  0)))) (show (nb077AlphaDummy330 x) ≠ (nb077AlphaDummy332 x) from (by
          unfold
            nb077AlphaDummy332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0325
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy327 F I), (nb077AlphaDummy330 x)), ((nb077AlphaDummy326 F I),
        (nb077AlphaDummy329 x)), ((nb077AlphaDummy325 F I), (nb077AlphaDummy328 x)),
        ((nb077AlphaDummy323 F I), (nb077AlphaDummy324 x)), ((nb077AlphaDummy319 F I),
        (nb077AlphaDummy321 x)), ((nb077AlphaDummy320 F I), (nb077AlphaDummy322 x)),
        ((nb077AlphaDummy345 F I), (nb077AlphaDummy346 x)), ((nb077AlphaDummy343 F I),
        (nb077AlphaDummy344 x)), ((nb077AlphaDummy312 F I), (nb077AlphaDummy314 x)),
        ((nb077AlphaDummy311 F I), (nb077AlphaDummy313 x)), ((nb077AlphaDummy341 F I),
        (nb077AlphaDummy342 x)), ((nb077AlphaDummy315 F I), (nb077AlphaDummy316 x)),
        ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I),
        (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
        (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F I),
        (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I),
        (nb077AlphaDummy018 x F I)), ((nb077AlphaDummy015 F I),
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy001 F I),
        (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077AlphaDummy319 F I))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy319 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy326 F
        I) ≠ (nb077AlphaDummy337 F I) from (by
          unfold
            nb077AlphaDummy337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0330
                    F I)
                  0)))) (show (nb077AlphaDummy329 x) ≠ (nb077AlphaDummy338 x) from (by
          unfold
            nb077AlphaDummy338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0331
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy326 F I) ≠
        (nb077AlphaDummy335 F I) from (by
          unfold
            nb077AlphaDummy335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0328
                    F I)
                  0)))) (show (nb077AlphaDummy329 x) ≠ (nb077AlphaDummy336 x) from (by
          unfold
            nb077AlphaDummy336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0329
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy319
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy326 F I) ≠ (nb077AlphaDummy337 F I) from
        (by
          unfold
            nb077AlphaDummy337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0330
                    F I)
                  0)))) (show (nb077AlphaDummy329 x) ≠ (nb077AlphaDummy338 x) from (by
          unfold
            nb077AlphaDummy338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0331
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy326 F I) ≠
        (nb077AlphaDummy335 F I) from (by
          unfold
            nb077AlphaDummy335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0328
                    F I)
                  0)))) (show (nb077AlphaDummy329 x) ≠ (nb077AlphaDummy336 x) from (by
          unfold
            nb077AlphaDummy336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0329
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy319
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy327 F
        I) ≠ (nb077AlphaDummy339 F I) from (by
          unfold
            nb077AlphaDummy339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0334
                    F I)
                  0)))) (show (nb077AlphaDummy330 x) ≠ (nb077AlphaDummy340 x) from (by
          unfold
            nb077AlphaDummy340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0335
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy327 F I) ≠
        (nb077AlphaDummy335 F I) from (by
          unfold
            nb077AlphaDummy335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0332
                    F I)
                  0)))) (show (nb077AlphaDummy330 x) ≠ (nb077AlphaDummy336 x) from (by
          unfold
            nb077AlphaDummy336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0333
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy327 F
        I) ≠ (nb077AlphaDummy339 F I) from (by
          unfold
            nb077AlphaDummy339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0334
                    F I)
                  0)))) (show (nb077AlphaDummy330 x) ≠ (nb077AlphaDummy340 x) from (by
          unfold
            nb077AlphaDummy340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0335
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy327 F I) ≠
        (nb077AlphaDummy335 F I) from (by
          unfold
            nb077AlphaDummy335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0332
                    F I)
                  0)))) (show (nb077AlphaDummy330 x) ≠ (nb077AlphaDummy336 x) from (by
          unfold
            nb077AlphaDummy336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0333
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077AlphaDummy319 F I) ≠ (nb077AlphaDummy323 F I) from
                                (by
                                  unfold nb077AlphaDummy323;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0316 F I)
                                          0))))
                              (show (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy324 x) from
                                (by
                                  unfold nb077AlphaDummy324;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0317 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb077AlphaDummy323 F I), (nb077AlphaDummy324 x)),
                              ((nb077AlphaDummy319 F I), (nb077AlphaDummy321 x)),
                              ((nb077AlphaDummy320 F I), (nb077AlphaDummy322 x)),
                              ((nb077AlphaDummy345 F I), (nb077AlphaDummy346 x)),
                              ((nb077AlphaDummy343 F I), (nb077AlphaDummy344 x)),
                              ((nb077AlphaDummy312 F I), (nb077AlphaDummy314 x)),
                              ((nb077AlphaDummy311 F I), (nb077AlphaDummy313 x)),
                              ((nb077AlphaDummy341 F I), (nb077AlphaDummy342 x)),
                              ((nb077AlphaDummy315 F I), (nb077AlphaDummy316 x)),
                              ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                              ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                              ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                              ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                              ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                              ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                              ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
                              ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
                              ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                              ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                              ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy319 F I) ≠ (nb077AlphaDummy323 F I) from (by
                                unfold nb077AlphaDummy323;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0316 F I) 0))))
                            (show (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy324 x) from (by
                                unfold nb077AlphaDummy324;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0317 x) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077AlphaDummy319 F I) ≠ (nb077AlphaDummy323 F I) from
                                (by
                                  unfold nb077AlphaDummy323;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0316 F I)
                                          0))))
                              (show (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy324 x) from
                                (by
                                  unfold nb077AlphaDummy324;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0317 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb077AlphaDummy323 F I), (nb077AlphaDummy324 x)),
                              ((nb077AlphaDummy319 F I), (nb077AlphaDummy321 x)),
                              ((nb077AlphaDummy320 F I), (nb077AlphaDummy322 x)),
                              ((nb077AlphaDummy345 F I), (nb077AlphaDummy346 x)),
                              ((nb077AlphaDummy343 F I), (nb077AlphaDummy344 x)),
                              ((nb077AlphaDummy312 F I), (nb077AlphaDummy314 x)),
                              ((nb077AlphaDummy311 F I), (nb077AlphaDummy313 x)),
                              ((nb077AlphaDummy341 F I), (nb077AlphaDummy342 x)),
                              ((nb077AlphaDummy315 F I), (nb077AlphaDummy316 x)),
                              ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                              ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                              ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                              ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                              ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                              ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                              ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
                              ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
                              ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                              ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                              ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb077_compact_envfresh_0124 (x : Var) (F : Class) (I : Class) :
    TEnvFresh
      [((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      ((synCcnv (synC1st))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb077AlphaDummy061 F I) (nb077AlphaDummy064 x)
      (nb077_wpp_notmem_0912 F I) (nb077_wpp_notmem_0913 x)
      (TEnvFresh.consFresh (nb077AlphaDummy060 F I) (nb077AlphaDummy063 x)
        (nb077_wpp_notmem_0914 F I) (nb077_wpp_notmem_0915 x)
        (TEnvFresh.consFresh (nb077AlphaDummy059 F I) (nb077AlphaDummy062 x)
          (nb077_wpp_notmem_0916 F I) (nb077_wpp_notmem_0917 x)
          (TEnvFresh.consFresh (nb077AlphaDummy065 F I) (nb077AlphaDummy066 x)
            (nb077_wpp_notmem_0918 F I) (nb077_wpp_notmem_0919 x)
            (TEnvFresh.consFresh (nb077AlphaDummy057 F I) (nb077AlphaDummy058 x F)
              (nb077_wpp_notmem_0920 F I) (nb077_wpp_notmem_0921 x F)
              (TEnvFresh.consFresh (nb077AlphaDummy055 F I) (nb077AlphaDummy056 x F)
                (nb077_wpp_notmem_0922 F I) (nb077_wpp_notmem_0923 x F)
                (TEnvFresh.consFresh (nb077AlphaDummy016 F I)
                  (nb077AlphaDummy018 x F I) (nb077_wpp_notmem_0924 F I)
                  (nb077_wpp_notmem_0925 x F I) (TEnvFresh.consFresh (nb077AlphaDummy015 F I)
                    (nb077AlphaDummy017 x F I) (nb077_wpp_notmem_0926 F I)
                    (nb077_wpp_notmem_0927 x F I)
                    (TEnvFresh.consFresh (nb077AlphaDummy001 F I)
                      (nb077AlphaDummy002 x F I) (nb077_wpp_notmem_0932 F I)
                      (nb077_wpp_notmem_0933 x F I)
                      (TEnvFresh.consFresh (nb077AlphaDummy004 F I)
                        (nb077AlphaDummy006 x F I) (nb077_wpp_notmem_0934 F I)
                        (nb077_wpp_notmem_0935 x F I)
                        (TEnvFresh.consFresh (nb077AlphaDummy003 F I)
                          (nb077AlphaDummy005 x F I) (nb077_wpp_notmem_0936 F I)
                          (nb077_wpp_notmem_0937 x F I)
                          (TEnvFresh.nil ((synCcnv (synC1st))).fv))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb077_wpp_refl_0124`. -/
@[expose]
noncomputable def nb077WppRefl0124 (x : Var) (F : Class) (I : Class) :
    TReflOn
      [((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      ((synCcnv (synC1st))).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0124 x F I)

theorem nb077_compact_envfresh_0125 (x : Var) (F : Class) (I : Class) :
    TEnvFresh
      [((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb077AlphaDummy057 F I) (nb077AlphaDummy058 x F)
      (nb077_wpp_notmem_0938 F I) (nb077_wpp_notmem_0939 x F)
      (TEnvFresh.consFresh (nb077AlphaDummy055 F I) (nb077AlphaDummy056 x F)
        (nb077_wpp_notmem_0940 F I) (nb077_wpp_notmem_0941 x F)
        (TEnvFresh.consFresh (nb077AlphaDummy016 F I) (nb077AlphaDummy018 x F I)
          (nb077_wpp_notmem_0942 F I) (nb077_wpp_notmem_0943 x F I)
          (TEnvFresh.consFresh (nb077AlphaDummy015 F I) (nb077AlphaDummy017 x F I)
            (nb077_wpp_notmem_0944 F I) (nb077_wpp_notmem_0945 x F I)
            (TEnvFresh.consFresh (nb077AlphaDummy001 F I) (nb077AlphaDummy002 x F I)
              (nb077_wpp_notmem_0950 F I) (nb077_wpp_notmem_0951 x F I)
              (TEnvFresh.consFresh (nb077AlphaDummy004 F I)
                (nb077AlphaDummy006 x F I) (nb077_wpp_notmem_0952 F I)
                (nb077_wpp_notmem_0953 x F I) (TEnvFresh.consFresh (nb077AlphaDummy003 F I)
                  (nb077AlphaDummy005 x F I) (nb077_wpp_notmem_0954 F I)
                  (nb077_wpp_notmem_0955 x F I) (TEnvFresh.nil
                    ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv))))))))

/-- Checked nominal proof certificate identified upstream as `nb077_wpp_refl_0125`. -/
@[expose]
noncomputable def nb077WppRefl0125 (x : Var) (F : Class) (I : Class) :
    TReflOn
      [((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0125 x F I)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
