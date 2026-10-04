/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C077C001Block009

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C077C001Part028`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb077_split_alpha_0015`. -/
@[expose]
noncomputable def nb077SplitAlpha0015 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077AlphaDummy317 F I), (nb077AlphaDummy318 x)),
        ((nb077AlphaDummy315 F I), (nb077AlphaDummy316 x)),
        ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy317 F I))
          (Class.cab (nb077AlphaDummy311 F I)
            (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy061 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                (synCphi (Class.cv (nb077AlphaDummy312 F I))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy317 F I))
            (Class.cab (nb077AlphaDummy311 F I)
              (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy061 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                  (synCphi (Class.cv (nb077AlphaDummy312 F I)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy318 x))
          (Class.cab (nb077AlphaDummy313 x)
            (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy064 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                (synCphi (Class.cv (nb077AlphaDummy314 x))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy318 x))
            (Class.cab (nb077AlphaDummy313 x)
              (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy064 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                  (synCphi (Class.cv (nb077AlphaDummy314 x))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077AlphaDummy061 F I) ≠ (nb077AlphaDummy312 F I) from (by
                      unfold nb077AlphaDummy312;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0308 F I) 1))))
                  (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy314 x) from (by
                      unfold nb077AlphaDummy314;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0310 x) 1))))
                  (TAlphaVar.there
                    (show (nb077AlphaDummy061 F I) ≠ (nb077AlphaDummy311 F I) from (by
                        unfold nb077AlphaDummy311;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0308 F I) 0))))
                    (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy313 x) from (by
                        unfold nb077AlphaDummy313;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0310 x) 0)))) (TAlphaVar.there
                      (show (nb077AlphaDummy061 F I) ≠ (nb077AlphaDummy317 F I) from (by
                          unfold nb077AlphaDummy317;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0312 F I) 0))))
                      (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy318 x) from (by
                          unfold nb077AlphaDummy318;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0313 x) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy061 F I) ≠ (nb077AlphaDummy315 F I) from (by
                            unfold nb077AlphaDummy315;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0309 F I) 0))))
                        (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy316 x) from (by
                            unfold nb077AlphaDummy316;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0311 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb077AlphaDummy061 F I))).fv ∪
                      ((Class.cv (nb077AlphaDummy060 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077AlphaDummy064 x))).fv ∪
                      ((Class.cv (nb077AlphaDummy063 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077AlphaDummy312 F I) ≠ (nb077AlphaDummy319 F I) from
                            (by
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
                                    (mem_lt_freshVar (nb077_support_mem_0315 x) 0))))
                          (TAlphaVar.there (show
                              (nb077AlphaDummy312 F I) ≠ (nb077AlphaDummy320 F I) from (by
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
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb077AlphaDummy312 F I))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb077AlphaDummy314 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy319 F I) ≠ (nb077AlphaDummy326 F I) from
        (by
          unfold nb077AlphaDummy326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0318 F I) 1)))) (show (nb077AlphaDummy321 x) ≠
        (nb077AlphaDummy329 x) from (by
          unfold nb077AlphaDummy329;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0319 x) 1)))) (TAlphaVar.there (show
        (nb077AlphaDummy319 F I) ≠ (nb077AlphaDummy325 F I) from (by
          unfold nb077AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0318 F I)
                  0)))) (show (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy328 x) from (by
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
                  (nb077_support_mem_0316 F I)
                  0)))) (show (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy324 x) from (by
          unfold nb077AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0317 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy327 F I), (nb077AlphaDummy330 x)), ((nb077AlphaDummy326 F I),
        (nb077AlphaDummy329 x)), ((nb077AlphaDummy325 F I), (nb077AlphaDummy328 x)),
        ((nb077AlphaDummy323 F I), (nb077AlphaDummy324 x)), ((nb077AlphaDummy319 F I),
        (nb077AlphaDummy321 x)), ((nb077AlphaDummy320 F I), (nb077AlphaDummy322 x)),
        ((nb077AlphaDummy312 F I), (nb077AlphaDummy314 x)), ((nb077AlphaDummy311 F I),
        (nb077AlphaDummy313 x)), ((nb077AlphaDummy317 F I), (nb077AlphaDummy318 x)),
        ((nb077AlphaDummy315 F I), (nb077AlphaDummy316 x)), ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb077AlphaDummy312 F I), (nb077AlphaDummy314 x)), ((nb077AlphaDummy311 F I),
        (nb077AlphaDummy313 x)), ((nb077AlphaDummy317 F I), (nb077AlphaDummy318 x)),
        ((nb077AlphaDummy315 F I), (nb077AlphaDummy316 x)), ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy319 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb077AlphaDummy319 F I))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb077AlphaDummy321 x))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy326
        F I) ≠ (nb077AlphaDummy337 F I) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy327
        F I) ≠ (nb077AlphaDummy339 F I) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy327
        F I) ≠ (nb077AlphaDummy339 F I) from (by
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
                                      (nb077AlphaDummy319 F I) ≠ (nb077AlphaDummy323 F I)
                                      from (by
                                        unfold nb077AlphaDummy323;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0316 F I) 0)))) (show
                                      (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy324 x) from
                                      (by
                                        unfold nb077AlphaDummy324;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0317 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed [((nb077AlphaDummy323 F I),
                                      (nb077AlphaDummy324 x)), ((nb077AlphaDummy319 F I),
                                      (nb077AlphaDummy321 x)), ((nb077AlphaDummy320 F I),
                                      (nb077AlphaDummy322 x)), ((nb077AlphaDummy312 F I),
                                      (nb077AlphaDummy314 x)), ((nb077AlphaDummy311 F I),
                                      (nb077AlphaDummy313 x)), ((nb077AlphaDummy317 F I),
                                      (nb077AlphaDummy318 x)), ((nb077AlphaDummy315 F I),
                                      (nb077AlphaDummy316 x)), ((nb077AlphaDummy061 F I),
                                      (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I),
                                      (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
                                      (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
                                      (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
                                      (nb077AlphaDummy058 x F)),
                                    ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                                    ((nb077AlphaDummy016 F I),
                                      (nb077AlphaDummy018 x F I)),
                                    ((nb077AlphaDummy015 F I),
                                      (nb077AlphaDummy017 x F I)),
                                    ((nb077AlphaDummy013 F I),
                                      (nb077AlphaDummy014 x F I)),
                                    ((nb077AlphaDummy011 F I),
                                      (nb077AlphaDummy012 x F I)),
                                    ((nb077AlphaDummy001 F I),
                                      (nb077AlphaDummy002 x F I)),
                                    ((nb077AlphaDummy004 F I),
                                      (nb077AlphaDummy006 x F I)),
                                    ((nb077AlphaDummy003 F I),
                                      (nb077AlphaDummy005 x F I))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb077AlphaDummy319 F I) ≠ (nb077AlphaDummy323 F I)
                                    from (by
                                      unfold nb077AlphaDummy323;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0316 F I)
                                              0)))) (show
                                    (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy324 x) from
                                    (by
                                      unfold nb077AlphaDummy324;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0317 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy319 F I) ≠ (nb077AlphaDummy323 F I)
                                      from (by
                                        unfold nb077AlphaDummy323;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0316 F I) 0)))) (show
                                      (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy324 x) from
                                      (by
                                        unfold nb077AlphaDummy324;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0317 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed [((nb077AlphaDummy323 F I),
                                      (nb077AlphaDummy324 x)), ((nb077AlphaDummy319 F I),
                                      (nb077AlphaDummy321 x)), ((nb077AlphaDummy320 F I),
                                      (nb077AlphaDummy322 x)), ((nb077AlphaDummy312 F I),
                                      (nb077AlphaDummy314 x)), ((nb077AlphaDummy311 F I),
                                      (nb077AlphaDummy313 x)), ((nb077AlphaDummy317 F I),
                                      (nb077AlphaDummy318 x)), ((nb077AlphaDummy315 F I),
                                      (nb077AlphaDummy316 x)), ((nb077AlphaDummy061 F I),
                                      (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I),
                                      (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
                                      (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
                                      (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
                                      (nb077AlphaDummy058 x F)),
                                    ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                                    ((nb077AlphaDummy016 F I),
                                      (nb077AlphaDummy018 x F I)),
                                    ((nb077AlphaDummy015 F I),
                                      (nb077AlphaDummy017 x F I)),
                                    ((nb077AlphaDummy013 F I),
                                      (nb077AlphaDummy014 x F I)),
                                    ((nb077AlphaDummy011 F I),
                                      (nb077AlphaDummy012 x F I)),
                                    ((nb077AlphaDummy001 F I),
                                      (nb077AlphaDummy002 x F I)),
                                    ((nb077AlphaDummy004 F I),
                                      (nb077AlphaDummy006 x F I)),
                                    ((nb077AlphaDummy003 F I),
                                      (nb077AlphaDummy005 x F I))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb077AlphaDummy061 F I) ≠ (nb077AlphaDummy312 F I) from (by
                        unfold nb077AlphaDummy312;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0308 F I) 1))))
                    (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy314 x) from (by
                        unfold nb077AlphaDummy314;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0310 x) 1)))) (TAlphaVar.there
                      (show (nb077AlphaDummy061 F I) ≠ (nb077AlphaDummy311 F I) from (by
                          unfold nb077AlphaDummy311;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0308 F I) 0))))
                      (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy313 x) from (by
                          unfold nb077AlphaDummy313;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0310 x) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy061 F I) ≠ (nb077AlphaDummy317 F I) from (by
                            unfold nb077AlphaDummy317;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0312 F I) 0))))
                        (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy318 x) from (by
                            unfold nb077AlphaDummy318;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0313 x) 0))))
                        (TAlphaVar.there
                          (show (nb077AlphaDummy061 F I) ≠ (nb077AlphaDummy315 F I) from
                            (by
                              unfold nb077AlphaDummy315;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0309 F I) 0))))
                          (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy316 x) from (by
                              unfold nb077AlphaDummy316;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0311 x) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb077AlphaDummy061 F I))).fv ∪
                        ((Class.cv (nb077AlphaDummy060 F I))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb077AlphaDummy064 x))).fv ∪
                        ((Class.cv (nb077AlphaDummy063 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy312 F I) ≠ (nb077AlphaDummy319 F I) from (by
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
                                      (mem_lt_freshVar (nb077_support_mem_0315 x) 0))))
                            (TAlphaVar.there (show
                                (nb077AlphaDummy312 F I) ≠ (nb077AlphaDummy320 F I) from
                                (by
                                  unfold nb077AlphaDummy320;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0314 F I)
                                          1))))
                              (show (nb077AlphaDummy314 x) ≠ (nb077AlphaDummy322 x) from
                                (by
                                  unfold nb077AlphaDummy322;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0315 x) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb077AlphaDummy312 F I))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb077AlphaDummy314 x))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy319 F I) ≠ (nb077AlphaDummy326 F I) from (by
          unfold nb077AlphaDummy326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0318 F I)
                  1)))) (show (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy329 x) from (by
          unfold nb077AlphaDummy329;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0319 x) 1)))) (TAlphaVar.there (show
        (nb077AlphaDummy319 F I) ≠ (nb077AlphaDummy325 F I) from (by
          unfold nb077AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0318 F I)
                  0)))) (show (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy328 x) from (by
          unfold nb077AlphaDummy328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0319 x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy319 F I) ≠
        (nb077AlphaDummy323 F I) from (by
          unfold nb077AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0316 F I)
                  0)))) (show (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy324 x) from (by
          unfold nb077AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0317 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy327 F I), (nb077AlphaDummy330 x)), ((nb077AlphaDummy326 F I),
        (nb077AlphaDummy329 x)), ((nb077AlphaDummy325 F I), (nb077AlphaDummy328 x)),
        ((nb077AlphaDummy323 F I), (nb077AlphaDummy324 x)), ((nb077AlphaDummy319 F I),
        (nb077AlphaDummy321 x)), ((nb077AlphaDummy320 F I), (nb077AlphaDummy322 x)),
        ((nb077AlphaDummy312 F I), (nb077AlphaDummy314 x)), ((nb077AlphaDummy311 F I),
        (nb077AlphaDummy313 x)), ((nb077AlphaDummy317 F I), (nb077AlphaDummy318 x)),
        ((nb077AlphaDummy315 F I), (nb077AlphaDummy316 x)), ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        ((nb077AlphaDummy312 F I), (nb077AlphaDummy314 x)), ((nb077AlphaDummy311 F I),
        (nb077AlphaDummy313 x)), ((nb077AlphaDummy317 F I), (nb077AlphaDummy318 x)),
        ((nb077AlphaDummy315 F I), (nb077AlphaDummy316 x)), ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy319 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077AlphaDummy321
        x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy319 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy326
        F I) ≠ (nb077AlphaDummy337 F I) from (by
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
        (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy327
        F I) ≠ (nb077AlphaDummy339 F I) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy327
        F I) ≠ (nb077AlphaDummy339 F I) from (by
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
                                        (nb077AlphaDummy319 F I) ≠
        (nb077AlphaDummy323 F I) from (by
                                          unfold nb077AlphaDummy323;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0316 F I) 0)))) (show
                                        (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy324 x)
                                        from (by
                                          unfold nb077AlphaDummy324;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0317 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb077AlphaDummy323 F I), (nb077AlphaDummy324 x)),
                                      ((nb077AlphaDummy319 F I), (nb077AlphaDummy321 x)),
                                      ((nb077AlphaDummy320 F I), (nb077AlphaDummy322 x)),
                                      ((nb077AlphaDummy312 F I), (nb077AlphaDummy314 x)),
                                      ((nb077AlphaDummy311 F I), (nb077AlphaDummy313 x)),
                                      ((nb077AlphaDummy317 F I), (nb077AlphaDummy318 x)),
                                      ((nb077AlphaDummy315 F I), (nb077AlphaDummy316 x)),
                                      ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                                      ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                                      ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                                      ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                                      ((nb077AlphaDummy057 F I),
                                        (nb077AlphaDummy058 x F)),
                                      ((nb077AlphaDummy055 F I),
                                        (nb077AlphaDummy056 x F)),
                                      ((nb077AlphaDummy016 F I),
                                        (nb077AlphaDummy018 x F I)),
                                      ((nb077AlphaDummy015 F I),
                                        (nb077AlphaDummy017 x F I)),
                                      ((nb077AlphaDummy013 F I),
                                        (nb077AlphaDummy014 x F I)),
                                      ((nb077AlphaDummy011 F I),
                                        (nb077AlphaDummy012 x F I)),
                                      ((nb077AlphaDummy001 F I),
                                        (nb077AlphaDummy002 x F I)),
                                      ((nb077AlphaDummy004 F I),
                                        (nb077AlphaDummy006 x F I)),
                                      ((nb077AlphaDummy003 F I),
                                        (nb077AlphaDummy005 x F I))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy319 F I) ≠ (nb077AlphaDummy323 F I)
                                      from (by
                                        unfold nb077AlphaDummy323;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0316 F I) 0)))) (show
                                      (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy324 x) from
                                      (by
                                        unfold nb077AlphaDummy324;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0317 x)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077AlphaDummy319 F I) ≠
        (nb077AlphaDummy323 F I) from (by
                                          unfold nb077AlphaDummy323;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0316 F I) 0)))) (show
                                        (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy324 x)
                                        from (by
                                          unfold nb077AlphaDummy324;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0317 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb077AlphaDummy323 F I), (nb077AlphaDummy324 x)),
                                      ((nb077AlphaDummy319 F I), (nb077AlphaDummy321 x)),
                                      ((nb077AlphaDummy320 F I), (nb077AlphaDummy322 x)),
                                      ((nb077AlphaDummy312 F I), (nb077AlphaDummy314 x)),
                                      ((nb077AlphaDummy311 F I), (nb077AlphaDummy313 x)),
                                      ((nb077AlphaDummy317 F I), (nb077AlphaDummy318 x)),
                                      ((nb077AlphaDummy315 F I), (nb077AlphaDummy316 x)),
                                      ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                                      ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                                      ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                                      ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                                      ((nb077AlphaDummy057 F I),
                                        (nb077AlphaDummy058 x F)),
                                      ((nb077AlphaDummy055 F I),
                                        (nb077AlphaDummy056 x F)),
                                      ((nb077AlphaDummy016 F I),
                                        (nb077AlphaDummy018 x F I)),
                                      ((nb077AlphaDummy015 F I),
                                        (nb077AlphaDummy017 x F I)),
                                      ((nb077AlphaDummy013 F I),
                                        (nb077AlphaDummy014 x F I)),
                                      ((nb077AlphaDummy011 F I),
                                        (nb077AlphaDummy012 x F I)),
                                      ((nb077AlphaDummy001 F I),
                                        (nb077AlphaDummy002 x F I)),
                                      ((nb077AlphaDummy004 F I),
                                        (nb077AlphaDummy006 x F I)),
                                      ((nb077AlphaDummy003 F I),
                                        (nb077AlphaDummy005 x F I))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part029`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb077_split_alpha_0016`. -/
@[expose]
noncomputable def nb077SplitAlpha0016 (x : Var) (F : Class) (I : Class) :
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
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
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
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy013 F I),
        (nb077AlphaDummy014 x F I)), ((nb077AlphaDummy011 F I),
        (nb077AlphaDummy012 x F I)), ((nb077AlphaDummy001 F I),
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
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
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
                            ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
                            ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
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
                            ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
                            ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
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
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
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
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy013 F I),
        (nb077AlphaDummy014 x F I)), ((nb077AlphaDummy011 F I),
        (nb077AlphaDummy012 x F I)), ((nb077AlphaDummy001 F I),
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
                              ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
                              ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
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
                              ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
                              ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
                              ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                              ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                              ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb077_wpp_notmem_0912 (F : Class) (I : Class) :
    (nb077AlphaDummy061 F I) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy061, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0100 F I)

theorem nb077_wpp_notmem_0913 (x : Var) :
    (nb077AlphaDummy064 x) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy064, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0101 x)

theorem nb077_wpp_notmem_0914 (F : Class) (I : Class) :
    (nb077AlphaDummy060 F I) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy060, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0064 F I)

theorem nb077_wpp_notmem_0915 (x : Var) :
    (nb077AlphaDummy063 x) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy063, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0065 x)

theorem nb077_wpp_notmem_0916 (F : Class) (I : Class) :
    (nb077AlphaDummy059 F I) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy059, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0066 F I)

theorem nb077_wpp_notmem_0917 (x : Var) :
    (nb077AlphaDummy062 x) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy062, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0067 x)

theorem nb077_wpp_notmem_0918 (F : Class) (I : Class) :
    (nb077AlphaDummy065 F I) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy065, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0068 F I)

theorem nb077_wpp_notmem_0919 (x : Var) :
    (nb077AlphaDummy066 x) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy066, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0069 x)

theorem nb077_wpp_notmem_0920 (F : Class) (I : Class) :
    (nb077AlphaDummy057 F I) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy057, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0070 F I)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part030`. -/


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

theorem nb077_wpp_notmem_0921 (x : Var) (F : Class) :
    (nb077AlphaDummy058 x F) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy058, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0071 x F)

theorem nb077_wpp_notmem_0922 (F : Class) (I : Class) :
    (nb077AlphaDummy055 F I) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy055, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0072 F I)

theorem nb077_wpp_notmem_0923 (x : Var) (F : Class) :
    (nb077AlphaDummy056 x F) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy056, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0073 x F)

theorem nb077_wpp_notmem_0924 (F : Class) (I : Class) :
    (nb077AlphaDummy016 F I) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy016, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0030 F I)

theorem nb077_wpp_notmem_0925 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy018 x F I) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy018, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0031 x F I)

theorem nb077_wpp_notmem_0926 (F : Class) (I : Class) :
    (nb077AlphaDummy015 F I) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy015, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0032 F I)

theorem nb077_wpp_notmem_0927 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy017 x F I) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy017, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0033 x F I)

theorem nb077_wpp_notmem_0928 (F : Class) (I : Class) :
    (nb077AlphaDummy013 F I) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy013, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0034 F I)

theorem nb077_wpp_notmem_0929 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy014 x F I) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy014, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0035 x F I)

theorem nb077_wpp_notmem_0930 (F : Class) (I : Class) :
    (nb077AlphaDummy011 F I) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy011, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0036 F I)

theorem nb077_wpp_notmem_0931 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy012 x F I) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy012, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0037 x F I)

theorem nb077_wpp_notmem_0932 (F : Class) (I : Class) :
    (nb077AlphaDummy001 F I) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy001, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0004 F I)

theorem nb077_wpp_notmem_0933 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy002 x F I) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy002, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0005 x F I)

theorem nb077_wpp_notmem_0934 (F : Class) (I : Class) :
    (nb077AlphaDummy004 F I) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy004, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0006 F I)

theorem nb077_wpp_notmem_0935 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy006 x F I) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy006, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0007 x F I)

theorem nb077_wpp_notmem_0936 (F : Class) (I : Class) :
    (nb077AlphaDummy003 F I) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy003, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0008 F I)

theorem nb077_wpp_notmem_0937 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy005 x F I) ∉ ((synCcnv (synC1st))).fv := by
  simpa only [nb077AlphaDummy005, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0009 x F I)

theorem nb077_compact_envfresh_0062 (x : Var) (F : Class) (I : Class) :
    TEnvFresh
      [((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
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
                    (TEnvFresh.consFresh (nb077AlphaDummy013 F I)
                      (nb077AlphaDummy014 x F I) (nb077_wpp_notmem_0928 F I)
                      (nb077_wpp_notmem_0929 x F I)
                      (TEnvFresh.consFresh (nb077AlphaDummy011 F I)
                        (nb077AlphaDummy012 x F I) (nb077_wpp_notmem_0930 F I)
                        (nb077_wpp_notmem_0931 x F I)
                        (TEnvFresh.consFresh (nb077AlphaDummy001 F I)
                          (nb077AlphaDummy002 x F I) (nb077_wpp_notmem_0932 F I)
                          (nb077_wpp_notmem_0933 x F I)
                          (TEnvFresh.consFresh (nb077AlphaDummy004 F I)
                            (nb077AlphaDummy006 x F I) (nb077_wpp_notmem_0934 F I)
                            (nb077_wpp_notmem_0935 x F I)
                            (TEnvFresh.consFresh (nb077AlphaDummy003 F I)
                              (nb077AlphaDummy005 x F I) (nb077_wpp_notmem_0936 F I)
                              (nb077_wpp_notmem_0937 x F I)
                              (TEnvFresh.nil ((synCcnv (synC1st))).fv))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb077_wpp_refl_0062`. -/
@[expose]
noncomputable def nb077WppRefl0062 (x : Var) (F : Class) (I : Class) :
    TReflOn
      [((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      ((synCcnv (synC1st))).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0062 x F I)

theorem nb077_focused_notmem_0010 (F : Class) (I : Class) :
    (nb077AlphaDummy057 F I) ∉ F.fv :=
  by
  change
    freshVar
        (((synCcom (synCcnv (synC1st)) (synCcom
                (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                  (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))
                (synC1st)))).fv ∪
          ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_ccom (synCcnv (synC2nd)) (synCcom F (synC2nd))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_ccom F (synC2nd)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb077_wpp_notmem_0938 (F : Class) (I : Class) :
    (nb077AlphaDummy057 F I) ∉
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  by
  simpa only [nb077AlphaDummy057, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0070 F I)
      (And.intro (nb077_focused_notmem_0010 F I) (nb077_compact_fv_empty_0070 F I)))

theorem nb077_focused_notmem_0011 (x : Var) (F : Class) :
    (nb077AlphaDummy058 x F) ∉ F.fv :=
  by
  change
    freshVar
        (((synCcom (synCcnv (synC1st))
              (synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))
                (synC1st)))).fv ∪
          ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_ccom (synCcnv (synC2nd)) (synCcom F (synC2nd))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_ccom F (synC2nd)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb077_wpp_notmem_0939 (x : Var) (F : Class) :
    (nb077AlphaDummy058 x F) ∉
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  by
  simpa only [nb077AlphaDummy058, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0071 x F)
      (And.intro (nb077_focused_notmem_0011 x F) (nb077_compact_fv_empty_0071 x F)))

theorem nb077_focused_notmem_0012 (F : Class) (I : Class) :
    (nb077AlphaDummy055 F I) ∉ F.fv :=
  by
  change
    freshVar
        (((synCnin (synCcom (synCcnv (synC1st)) (synCcom
                  (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                    (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st)))
              (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd))))).fv ∪ ((synCnin
              (synCcom (synCcnv (synC1st)) (synCcom
                  (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                    (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st)))
              (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd))))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin
      (synCcom (synCcnv (synC1st)) (synCcom (synCmpt (nb077AlphaDummy000 F I) (synCvv)
            (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st)))
      (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_ccom (synCcnv (synC2nd)) (synCcom F (synC2nd))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_ccom F (synC2nd)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb077_wpp_notmem_0940 (F : Class) (I : Class) :
    (nb077AlphaDummy055 F I) ∉
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  by
  simpa only [nb077AlphaDummy055, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0072 F I)
      (And.intro (nb077_focused_notmem_0012 F I) (nb077_compact_fv_empty_0072 F I)))

theorem nb077_focused_notmem_0013 (x : Var) (F : Class) :
    (nb077AlphaDummy056 x F) ∉ F.fv :=
  by
  change
    freshVar
        (((synCnin (synCcom (synCcnv (synC1st))
                (synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st)))
              (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd))))).fv ∪ ((synCnin
              (synCcom (synCcnv (synC1st))
                (synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st)))
              (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd))))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin
      (synCcom (synCcnv (synC1st))
        (synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st)))
      (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_ccom (synCcnv (synC2nd)) (synCcom F (synC2nd))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_ccom F (synC2nd)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb077_wpp_notmem_0941 (x : Var) (F : Class) :
    (nb077AlphaDummy056 x F) ∉
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  by
  simpa only [nb077AlphaDummy056, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0073 x F)
      (And.intro (nb077_focused_notmem_0013 x F) (nb077_compact_fv_empty_0073 x F)))

theorem nb077_focused_notmem_0014 (F : Class) (I : Class) :
    (nb077AlphaDummy016 F I) ∉ F.fv :=
  by
  change
    freshVar
        (((synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)).fv ∪
          ((Class.cv (nb077AlphaDummy001 F I))).fv)
        1 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cpprod
      (synCmpt (nb077AlphaDummy000 F I) (synCvv)
        (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))
      F]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0942 (F : Class) (I : Class) :
    (nb077AlphaDummy016 F I) ∉
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  by
  simpa only [nb077AlphaDummy016, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0030 F I)
      (And.intro (nb077_focused_notmem_0014 F I) (nb077_compact_fv_empty_0030 F I)))

theorem nb077_focused_notmem_0015 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy018 x F I) ∉ F.fv :=
  by
  change
    freshVar
        (((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)).fv ∪
          ((Class.cv (nb077AlphaDummy002 x F I))).fv)
        1 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0943 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy018 x F I) ∉
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  by
  simpa only [nb077AlphaDummy018, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0031 x F I)
      (And.intro (nb077_focused_notmem_0015 x F I) (nb077_compact_fv_empty_0031 x F I)))

theorem nb077_focused_notmem_0016 (F : Class) (I : Class) :
    (nb077AlphaDummy015 F I) ∉ F.fv :=
  by
  change
    freshVar
        (((synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)).fv ∪
          ((Class.cv (nb077AlphaDummy001 F I))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cpprod
      (synCmpt (nb077AlphaDummy000 F I) (synCvv)
        (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))
      F]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0944 (F : Class) (I : Class) :
    (nb077AlphaDummy015 F I) ∉
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  by
  simpa only [nb077AlphaDummy015, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0032 F I)
      (And.intro (nb077_focused_notmem_0016 F I) (nb077_compact_fv_empty_0032 F I)))

theorem nb077_focused_notmem_0017 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy017 x F I) ∉ F.fv :=
  by
  change
    freshVar
        (((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)).fv ∪
          ((Class.cv (nb077AlphaDummy002 x F I))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0945 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy017 x F I) ∉
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  by
  simpa only [nb077AlphaDummy017, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0033 x F I)
      (And.intro (nb077_focused_notmem_0017 x F I) (nb077_compact_fv_empty_0033 x F I)))

theorem nb077_focused_notmem_0018 (F : Class) (I : Class) :
    (nb077AlphaDummy013 F I) ∉ F.fv :=
  by
  change
    freshVar
        (((synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                  (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
              (Class.cv (nb077AlphaDummy001 F I)))).fv ∪
          ((Class.cv (nb077AlphaDummy001 F I))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cima
      (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
          (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
      (Class.cv (nb077AlphaDummy001 F I))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cpprod
      (synCmpt (nb077AlphaDummy000 F I) (synCvv)
        (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))
      F]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0946 (F : Class) (I : Class) :
    (nb077AlphaDummy013 F I) ∉
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  by
  simpa only [nb077AlphaDummy013, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0034 F I)
      (And.intro (nb077_focused_notmem_0018 F I) (nb077_compact_fv_empty_0034 F I)))

theorem nb077_focused_notmem_0019 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy014 x F I) ∉ F.fv :=
  by
  change
    freshVar
        (((synCima (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
              (Class.cv (nb077AlphaDummy002 x F I)))).fv ∪
          ((Class.cv (nb077AlphaDummy002 x F I))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cima (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
      (Class.cv (nb077AlphaDummy002 x F I))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0947 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy014 x F I) ∉
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  by
  simpa only [nb077AlphaDummy014, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0035 x F I)
      (And.intro (nb077_focused_notmem_0019 x F I) (nb077_compact_fv_empty_0035 x F I)))

theorem nb077_focused_notmem_0020 (F : Class) (I : Class) :
    (nb077AlphaDummy011 F I) ∉ F.fv :=
  by
  change
    freshVar
        (((synCnin (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                    (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
                (Class.cv (nb077AlphaDummy001 F I)))
              (Class.cv (nb077AlphaDummy001 F I)))).fv ∪ ((synCnin (synCima (synCpprod
                  (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                    (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
                (Class.cv (nb077AlphaDummy001 F I)))
              (Class.cv (nb077AlphaDummy001 F I)))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin
      (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
            (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
        (Class.cv (nb077AlphaDummy001 F I)))
      (Class.cv (nb077AlphaDummy001 F I))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cima
      (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
          (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
      (Class.cv (nb077AlphaDummy001 F I))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cpprod
      (synCmpt (nb077AlphaDummy000 F I) (synCvv)
        (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))
      F]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0948 (F : Class) (I : Class) :
    (nb077AlphaDummy011 F I) ∉
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  by
  simpa only [nb077AlphaDummy011, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0036 F I)
      (And.intro (nb077_focused_notmem_0020 F I) (nb077_compact_fv_empty_0036 F I)))

theorem nb077_focused_notmem_0021 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy012 x F I) ∉ F.fv :=
  by
  change
    freshVar
        (((synCnin (synCima
                (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
                (Class.cv (nb077AlphaDummy002 x F I)))
              (Class.cv (nb077AlphaDummy002 x F I)))).fv ∪ ((synCnin (synCima
                (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
                (Class.cv (nb077AlphaDummy002 x F I)))
              (Class.cv (nb077AlphaDummy002 x F I)))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin
      (synCima (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
        (Class.cv (nb077AlphaDummy002 x F I)))
      (Class.cv (nb077AlphaDummy002 x F I))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cima (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
      (Class.cv (nb077AlphaDummy002 x F I))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0949 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy012 x F I) ∉
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  by
  simpa only [nb077AlphaDummy012, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0037 x F I)
      (And.intro (nb077_focused_notmem_0021 x F I) (nb077_compact_fv_empty_0037 x F I)))

theorem nb077_focused_notmem_0022 (F : Class) (I : Class) :
    (nb077AlphaDummy001 F I) ∉ F.fv :=
  by
  change
    freshVar
        (((synCsn (synCop (synC0c) I))).fv ∪ ((synCpprod
              (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpprod
      (synCmpt (nb077AlphaDummy000 F I) (synCvv)
        (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))
      F]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0950 (F : Class) (I : Class) :
    (nb077AlphaDummy001 F I) ∉
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  by
  simpa only [nb077AlphaDummy001, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0004 F I)
      (And.intro (nb077_focused_notmem_0022 F I) (nb077_compact_fv_empty_0004 F I)))

theorem nb077_focused_notmem_0023 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy002 x F I) ∉ F.fv :=
  by
  change
    freshVar
        (((synCsn (synCop (synC0c) I))).fv ∪
          ((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0951 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy002 x F I) ∉
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  by
  simpa only [nb077AlphaDummy002, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0005 x F I)
      (And.intro (nb077_focused_notmem_0023 x F I) (nb077_compact_fv_empty_0005 x F I)))

theorem nb077_focused_notmem_0024 (F : Class) (I : Class) :
    (nb077AlphaDummy004 F I) ∉ F.fv :=
  by
  change
    freshVar
        (((Class.cab (nb077AlphaDummy001 F I) (synWa
              (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I)))
              (synWss (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                      (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
                  (Class.cv (nb077AlphaDummy001 F I)))
                (Class.cv (nb077AlphaDummy001 F I)))))).fv)
        1 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_class_cab (nb077AlphaDummy001 F I)
      (synWa (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I)))
        (synWss (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
            (Class.cv (nb077AlphaDummy001 F I))) (Class.cv (nb077AlphaDummy001 F I))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb077_focused_notmem_0022 F I)) (h_eq ▸ hu)
  · rw [fv_syn_wa
        (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I)))
        (synWss (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
            (Class.cv (nb077AlphaDummy001 F I))) (Class.cv (nb077AlphaDummy001 F I)))]
    rw [Finset.mem_union]
    right
    rw [fv_syn_wss
        (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
          (Class.cv (nb077AlphaDummy001 F I)))
        (Class.cv (nb077AlphaDummy001 F I))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_cima
        (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
            (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
        (Class.cv (nb077AlphaDummy001 F I))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_cpprod
        (synCmpt (nb077AlphaDummy000 F I) (synCvv)
          (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))
        F]
    rw [Finset.mem_union]
    right
    exact hu

theorem nb077_wpp_notmem_0952 (F : Class) (I : Class) :
    (nb077AlphaDummy004 F I) ∉
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  by
  simpa only [nb077AlphaDummy004, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0006 F I)
      (And.intro (nb077_focused_notmem_0024 F I) (nb077_compact_fv_empty_0006 F I)))

theorem nb077_focused_notmem_0025 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy006 x F I) ∉ F.fv :=
  by
  change
    freshVar
        (((Class.cab (nb077AlphaDummy002 x F I) (synWa
              (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy002 x F I)))
              (synWss (synCima
                  (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
                  (Class.cv (nb077AlphaDummy002 x F I)))
                (Class.cv (nb077AlphaDummy002 x F I)))))).fv)
        1 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_class_cab (nb077AlphaDummy002 x F I)
      (synWa (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy002 x F I)))
        (synWss (synCima
            (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
            (Class.cv (nb077AlphaDummy002 x F I)))
          (Class.cv (nb077AlphaDummy002 x F I))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb077_focused_notmem_0023 x F I)) (h_eq ▸ hu)
  · rw [fv_syn_wa
        (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy002 x F I)))
        (synWss (synCima
            (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
            (Class.cv (nb077AlphaDummy002 x F I))) (Class.cv (nb077AlphaDummy002 x F I)))]
    rw [Finset.mem_union]
    right
    rw [fv_syn_wss
        (synCima (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
          (Class.cv (nb077AlphaDummy002 x F I)))
        (Class.cv (nb077AlphaDummy002 x F I))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_cima
        (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
        (Class.cv (nb077AlphaDummy002 x F I))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_cpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F]
    rw [Finset.mem_union]
    right
    exact hu

theorem nb077_wpp_notmem_0953 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy006 x F I) ∉
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  by
  simpa only [nb077AlphaDummy006, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0007 x F I)
      (And.intro (nb077_focused_notmem_0025 x F I) (nb077_compact_fv_empty_0007 x F I)))

theorem nb077_focused_notmem_0026 (F : Class) (I : Class) :
    (nb077AlphaDummy003 F I) ∉ F.fv :=
  by
  change
    freshVar
        (((Class.cab (nb077AlphaDummy001 F I) (synWa
              (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I)))
              (synWss (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                      (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
                  (Class.cv (nb077AlphaDummy001 F I)))
                (Class.cv (nb077AlphaDummy001 F I)))))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_class_cab (nb077AlphaDummy001 F I)
      (synWa (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I)))
        (synWss (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
            (Class.cv (nb077AlphaDummy001 F I))) (Class.cv (nb077AlphaDummy001 F I))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb077_focused_notmem_0022 F I)) (h_eq ▸ hu)
  · rw [fv_syn_wa
        (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I)))
        (synWss (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
            (Class.cv (nb077AlphaDummy001 F I))) (Class.cv (nb077AlphaDummy001 F I)))]
    rw [Finset.mem_union]
    right
    rw [fv_syn_wss
        (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
          (Class.cv (nb077AlphaDummy001 F I)))
        (Class.cv (nb077AlphaDummy001 F I))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_cima
        (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
            (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
        (Class.cv (nb077AlphaDummy001 F I))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_cpprod
        (synCmpt (nb077AlphaDummy000 F I) (synCvv)
          (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))
        F]
    rw [Finset.mem_union]
    right
    exact hu

theorem nb077_wpp_notmem_0954 (F : Class) (I : Class) :
    (nb077AlphaDummy003 F I) ∉
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  by
  simpa only [nb077AlphaDummy003, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0008 F I)
      (And.intro (nb077_focused_notmem_0026 F I) (nb077_compact_fv_empty_0008 F I)))

theorem nb077_focused_notmem_0027 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy005 x F I) ∉ F.fv :=
  by
  change
    freshVar
        (((Class.cab (nb077AlphaDummy002 x F I) (synWa
              (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy002 x F I)))
              (synWss (synCima
                  (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
                  (Class.cv (nb077AlphaDummy002 x F I)))
                (Class.cv (nb077AlphaDummy002 x F I)))))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_class_cab (nb077AlphaDummy002 x F I)
      (synWa (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy002 x F I)))
        (synWss (synCima
            (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
            (Class.cv (nb077AlphaDummy002 x F I)))
          (Class.cv (nb077AlphaDummy002 x F I))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb077_focused_notmem_0023 x F I)) (h_eq ▸ hu)
  · rw [fv_syn_wa
        (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy002 x F I)))
        (synWss (synCima
            (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
            (Class.cv (nb077AlphaDummy002 x F I))) (Class.cv (nb077AlphaDummy002 x F I)))]
    rw [Finset.mem_union]
    right
    rw [fv_syn_wss
        (synCima (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
          (Class.cv (nb077AlphaDummy002 x F I)))
        (Class.cv (nb077AlphaDummy002 x F I))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_cima
        (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
        (Class.cv (nb077AlphaDummy002 x F I))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_cpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F]
    rw [Finset.mem_union]
    right
    exact hu

theorem nb077_wpp_notmem_0955 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy005 x F I) ∉
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  by
  simpa only [nb077AlphaDummy005, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0009 x F I)
      (And.intro (nb077_focused_notmem_0027 x F I) (nb077_compact_fv_empty_0009 x F I)))

theorem nb077_compact_envfresh_0063 (x : Var) (F : Class) (I : Class) :
    TEnvFresh
      [((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
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
            (TEnvFresh.consFresh (nb077AlphaDummy013 F I) (nb077AlphaDummy014 x F I)
              (nb077_wpp_notmem_0946 F I) (nb077_wpp_notmem_0947 x F I)
              (TEnvFresh.consFresh (nb077AlphaDummy011 F I)
                (nb077AlphaDummy012 x F I) (nb077_wpp_notmem_0948 F I)
                (nb077_wpp_notmem_0949 x F I) (TEnvFresh.consFresh (nb077AlphaDummy001 F I)
                  (nb077AlphaDummy002 x F I) (nb077_wpp_notmem_0950 F I)
                  (nb077_wpp_notmem_0951 x F I) (TEnvFresh.consFresh (nb077AlphaDummy004 F I)
                    (nb077AlphaDummy006 x F I) (nb077_wpp_notmem_0952 F I)
                    (nb077_wpp_notmem_0953 x F I)
                    (TEnvFresh.consFresh (nb077AlphaDummy003 F I)
                      (nb077AlphaDummy005 x F I) (nb077_wpp_notmem_0954 F I)
                      (nb077_wpp_notmem_0955 x F I) (TEnvFresh.nil
                        ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv))))))))))

/-- Checked nominal proof certificate identified upstream as `nb077_wpp_refl_0063`. -/
@[expose]
noncomputable def nb077WppRefl0063 (x : Var) (F : Class) (I : Class) :
    TReflOn
      [((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0063 x F I)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
