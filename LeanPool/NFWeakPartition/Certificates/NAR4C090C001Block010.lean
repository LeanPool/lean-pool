/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block009

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part034`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0010`. -/
@[expose]
noncomputable def nb090SplitAlpha0010 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy241 A), (nb090AlphaDummy242 h)),
        ((nb090AlphaDummy239 A), (nb090AlphaDummy240 h)),
        ((nb090AlphaDummy208 A), (nb090AlphaDummy210 h)),
        ((nb090AlphaDummy207 A), (nb090AlphaDummy209 h)),
        ((nb090AlphaDummy237 A), (nb090AlphaDummy238 h)),
        ((nb090AlphaDummy211 A), (nb090AlphaDummy212 h)),
        ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy241 A))
          (synCphi (Class.cv (nb090AlphaDummy208 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy241 A))
            (synCphi (Class.cv (nb090AlphaDummy208 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy242 h))
          (synCphi (Class.cv (nb090AlphaDummy210 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy242 h))
            (synCphi (Class.cv (nb090AlphaDummy210 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy208 A) ≠ (nb090AlphaDummy215 A) from (by
                      unfold nb090AlphaDummy215;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0220 A) 0))))
                  (show (nb090AlphaDummy210 h) ≠ (nb090AlphaDummy217 h) from (by
                      unfold nb090AlphaDummy217;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0221 h) 0))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy208 A) ≠ (nb090AlphaDummy216 A) from (by
                        unfold nb090AlphaDummy216;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0220 A) 1))))
                    (show (nb090AlphaDummy210 h) ≠ (nb090AlphaDummy218 h) from (by
                        unfold nb090AlphaDummy218;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0221 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy208 A) ≠ (nb090AlphaDummy241 A) from (by
                          unfold nb090AlphaDummy241;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0250 A) 0))))
                      (show (nb090AlphaDummy210 h) ≠ (nb090AlphaDummy242 h) from (by
                          unfold nb090AlphaDummy242;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0251 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy208 A) ≠ (nb090AlphaDummy239 A) from (by
                            unfold nb090AlphaDummy239;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0248 A) 0))))
                        (show (nb090AlphaDummy210 h) ≠ (nb090AlphaDummy240 h) from (by
                            unfold nb090AlphaDummy240;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0249 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy208 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy210 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy222 A) from
                                      (by
                                        unfold nb090AlphaDummy222;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0224 A)
                                                1)))) (show (nb090AlphaDummy217 h) ≠
                                        (nb090AlphaDummy225 h) from (by
                                        unfold nb090AlphaDummy225;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0225 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy221 A)
                                        from (by
                                          unfold nb090AlphaDummy221;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0224 A) 0)))) (show
                                        (nb090AlphaDummy217 h) ≠ (nb090AlphaDummy224 h)
                                        from (by
                                          unfold nb090AlphaDummy224;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0225 h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy215 A) ≠
        (nb090AlphaDummy219 A) from (by
          unfold nb090AlphaDummy219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0222 A) 0)))) (show (nb090AlphaDummy217 h) ≠
        (nb090AlphaDummy220 h) from (by
          unfold nb090AlphaDummy220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0223 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb090AlphaDummy223 A),
        (nb090AlphaDummy226 h)), ((nb090AlphaDummy222 A), (nb090AlphaDummy225 h)),
                                        ((nb090AlphaDummy221 A), (nb090AlphaDummy224 h)),
                                        ((nb090AlphaDummy219 A), (nb090AlphaDummy220 h)),
                                        ((nb090AlphaDummy215 A), (nb090AlphaDummy217 h)),
                                        ((nb090AlphaDummy216 A), (nb090AlphaDummy218 h)),
                                        ((nb090AlphaDummy241 A), (nb090AlphaDummy242 h)),
                                        ((nb090AlphaDummy239 A), (nb090AlphaDummy240 h)),
                                        ((nb090AlphaDummy208 A), (nb090AlphaDummy210 h)),
                                        ((nb090AlphaDummy207 A), (nb090AlphaDummy209 h)),
                                        ((nb090AlphaDummy237 A), (nb090AlphaDummy238 h)),
                                        ((nb090AlphaDummy211 A), (nb090AlphaDummy212 h)),
                                        ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                                        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                        ((nb090AlphaDummy000 A), h),
                                        ((nb090AlphaDummy002 A), v),
                                        ((nb090AlphaDummy001 A), u),
                                        ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy222 A) ≠ (nb090AlphaDummy229 A) from (by
          unfold
            nb090AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0228
                    A)
                  0)))) (show (nb090AlphaDummy225 h) ≠ (nb090AlphaDummy230 h) from (by
          unfold
            nb090AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0229
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy222 A) ≠
        (nb090AlphaDummy227 A) from (by
          unfold
            nb090AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0226
                    A)
                  0)))) (show (nb090AlphaDummy225 h) ≠ (nb090AlphaDummy228 h) from (by
          unfold
            nb090AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0227
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy215
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy223 A) ≠
        (nb090AlphaDummy229 A) from (by
          unfold
            nb090AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0232
                    A)
                  0)))) (show (nb090AlphaDummy226 h) ≠ (nb090AlphaDummy230 h) from (by
          unfold
            nb090AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0233
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy223 A) ≠
        (nb090AlphaDummy227 A) from (by
          unfold
            nb090AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0230
                    A)
                  0)))) (show (nb090AlphaDummy226 h) ≠ (nb090AlphaDummy228 h) from (by
          unfold
            nb090AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0231
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy222 A) ≠ (nb090AlphaDummy229 A) from (by
          unfold
            nb090AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0228
                    A)
                  0)))) (show (nb090AlphaDummy225 h) ≠ (nb090AlphaDummy230 h) from (by
          unfold
            nb090AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0229
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy222 A) ≠
        (nb090AlphaDummy227 A) from (by
          unfold
            nb090AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0226
                    A)
                  0)))) (show (nb090AlphaDummy225 h) ≠ (nb090AlphaDummy228 h) from (by
          unfold
            nb090AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0227
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy215
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy223 A) ≠
        (nb090AlphaDummy229 A) from (by
          unfold
            nb090AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0232
                    A)
                  0)))) (show (nb090AlphaDummy226 h) ≠ (nb090AlphaDummy230 h) from (by
          unfold
            nb090AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0233
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy223 A) ≠
        (nb090AlphaDummy227 A) from (by
          unfold
            nb090AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0230
                    A)
                  0)))) (show (nb090AlphaDummy226 h) ≠ (nb090AlphaDummy228 h) from (by
          unfold
            nb090AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0231
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb090AlphaDummy223 A), (nb090AlphaDummy226 h)),
        ((nb090AlphaDummy222 A), (nb090AlphaDummy225 h)), ((nb090AlphaDummy221 A),
        (nb090AlphaDummy224 h)), ((nb090AlphaDummy219 A), (nb090AlphaDummy220 h)),
        ((nb090AlphaDummy215 A), (nb090AlphaDummy217 h)), ((nb090AlphaDummy216 A),
        (nb090AlphaDummy218 h)), ((nb090AlphaDummy241 A), (nb090AlphaDummy242 h)),
        ((nb090AlphaDummy239 A), (nb090AlphaDummy240 h)), ((nb090AlphaDummy208 A),
        (nb090AlphaDummy210 h)), ((nb090AlphaDummy207 A), (nb090AlphaDummy209 h)),
        ((nb090AlphaDummy237 A), (nb090AlphaDummy238 h)), ((nb090AlphaDummy211 A),
        (nb090AlphaDummy212 h)), ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A),
        (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy215 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy215 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy222 A) ≠ (nb090AlphaDummy233 A) from (by
          unfold
            nb090AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0236
                    A)
                  0)))) (show (nb090AlphaDummy225 h) ≠ (nb090AlphaDummy234 h) from (by
          unfold
            nb090AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0237
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy222 A) ≠
        (nb090AlphaDummy231 A) from (by
          unfold
            nb090AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0234
                    A)
                  0)))) (show (nb090AlphaDummy225 h) ≠ (nb090AlphaDummy232 h) from (by
          unfold
            nb090AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0235
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy215
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy222 A) ≠
        (nb090AlphaDummy233 A) from (by
          unfold
            nb090AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0236
                    A)
                  0)))) (show (nb090AlphaDummy225 h) ≠ (nb090AlphaDummy234 h) from (by
          unfold
            nb090AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0237
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy222 A) ≠
        (nb090AlphaDummy231 A) from (by
          unfold
            nb090AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0234
                    A)
                  0)))) (show (nb090AlphaDummy225 h) ≠ (nb090AlphaDummy232 h) from (by
          unfold
            nb090AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0235
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy215
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy223 A) ≠ (nb090AlphaDummy235 A) from (by
          unfold
            nb090AlphaDummy235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0240
                    A)
                  0)))) (show (nb090AlphaDummy226 h) ≠ (nb090AlphaDummy236 h) from (by
          unfold
            nb090AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0241
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy223 A) ≠
        (nb090AlphaDummy231 A) from (by
          unfold
            nb090AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0238
                    A)
                  0)))) (show (nb090AlphaDummy226 h) ≠ (nb090AlphaDummy232 h) from (by
          unfold
            nb090AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0239
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy223 A) ≠ (nb090AlphaDummy235 A) from (by
          unfold
            nb090AlphaDummy235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0240
                    A)
                  0)))) (show (nb090AlphaDummy226 h) ≠ (nb090AlphaDummy236 h) from (by
          unfold
            nb090AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0241
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy223 A) ≠
        (nb090AlphaDummy231 A) from (by
          unfold
            nb090AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0238
                    A)
                  0)))) (show (nb090AlphaDummy226 h) ≠ (nb090AlphaDummy232 h) from (by
          unfold
            nb090AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0239
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy219 A) from (by
                                unfold nb090AlphaDummy219;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0222 A) 0))))
                            (show (nb090AlphaDummy217 h) ≠ (nb090AlphaDummy220 h) from (by
                                unfold nb090AlphaDummy220;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0223 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy219 A), (nb090AlphaDummy220 h)),
                            ((nb090AlphaDummy215 A), (nb090AlphaDummy217 h)),
                            ((nb090AlphaDummy216 A), (nb090AlphaDummy218 h)),
                            ((nb090AlphaDummy241 A), (nb090AlphaDummy242 h)),
                            ((nb090AlphaDummy239 A), (nb090AlphaDummy240 h)),
                            ((nb090AlphaDummy208 A), (nb090AlphaDummy210 h)),
                            ((nb090AlphaDummy207 A), (nb090AlphaDummy209 h)),
                            ((nb090AlphaDummy237 A), (nb090AlphaDummy238 h)),
                            ((nb090AlphaDummy211 A), (nb090AlphaDummy212 h)),
                            ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                            ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                            ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                            ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                            ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                            ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy219 A) from (by
                              unfold nb090AlphaDummy219;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0222 A) 0))))
                          (show (nb090AlphaDummy217 h) ≠ (nb090AlphaDummy220 h) from (by
                              unfold nb090AlphaDummy220;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0223 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy219 A) from (by
                                unfold nb090AlphaDummy219;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0222 A) 0))))
                            (show (nb090AlphaDummy217 h) ≠ (nb090AlphaDummy220 h) from (by
                                unfold nb090AlphaDummy220;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0223 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy219 A), (nb090AlphaDummy220 h)),
                            ((nb090AlphaDummy215 A), (nb090AlphaDummy217 h)),
                            ((nb090AlphaDummy216 A), (nb090AlphaDummy218 h)),
                            ((nb090AlphaDummy241 A), (nb090AlphaDummy242 h)),
                            ((nb090AlphaDummy239 A), (nb090AlphaDummy240 h)),
                            ((nb090AlphaDummy208 A), (nb090AlphaDummy210 h)),
                            ((nb090AlphaDummy207 A), (nb090AlphaDummy209 h)),
                            ((nb090AlphaDummy237 A), (nb090AlphaDummy238 h)),
                            ((nb090AlphaDummy211 A), (nb090AlphaDummy212 h)),
                            ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                            ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                            ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                            ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                            ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                            ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090AlphaDummy208 A) ≠ (nb090AlphaDummy215 A) from (by
                        unfold nb090AlphaDummy215;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0220 A) 0))))
                    (show (nb090AlphaDummy210 h) ≠ (nb090AlphaDummy217 h) from (by
                        unfold nb090AlphaDummy217;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0221 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy208 A) ≠ (nb090AlphaDummy216 A) from (by
                          unfold nb090AlphaDummy216;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0220 A) 1))))
                      (show (nb090AlphaDummy210 h) ≠ (nb090AlphaDummy218 h) from (by
                          unfold nb090AlphaDummy218;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0221 h) 1))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy208 A) ≠ (nb090AlphaDummy241 A) from (by
                            unfold nb090AlphaDummy241;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0250 A) 0))))
                        (show (nb090AlphaDummy210 h) ≠ (nb090AlphaDummy242 h) from (by
                            unfold nb090AlphaDummy242;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0251 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy208 A) ≠ (nb090AlphaDummy239 A) from (by
                              unfold nb090AlphaDummy239;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0248 A) 0))))
                          (show (nb090AlphaDummy210 h) ≠ (nb090AlphaDummy240 h) from (by
                              unfold nb090AlphaDummy240;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0249 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090AlphaDummy208 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy210 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090AlphaDummy215 A) ≠
        (nb090AlphaDummy222 A) from (by
                                          unfold nb090AlphaDummy222;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0224 A) 1)))) (show
                                        (nb090AlphaDummy217 h) ≠ (nb090AlphaDummy225 h)
                                        from (by
                                          unfold nb090AlphaDummy225;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0225 h) 1))))
                                      (TAlphaVar.there (show (nb090AlphaDummy215 A) ≠
        (nb090AlphaDummy221 A) from (by
          unfold nb090AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0224 A) 0)))) (show (nb090AlphaDummy217 h) ≠
        (nb090AlphaDummy224 h) from (by
          unfold nb090AlphaDummy224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0225 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy219 A) from (by
          unfold nb090AlphaDummy219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0222 A) 0)))) (show (nb090AlphaDummy217 h) ≠
        (nb090AlphaDummy220 h) from (by
          unfold nb090AlphaDummy220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0223 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy223 A),
        (nb090AlphaDummy226 h)), ((nb090AlphaDummy222 A), (nb090AlphaDummy225 h)),
        ((nb090AlphaDummy221 A), (nb090AlphaDummy224 h)), ((nb090AlphaDummy219 A),
        (nb090AlphaDummy220 h)), ((nb090AlphaDummy215 A), (nb090AlphaDummy217 h)),
        ((nb090AlphaDummy216 A), (nb090AlphaDummy218 h)), ((nb090AlphaDummy241 A),
        (nb090AlphaDummy242 h)), ((nb090AlphaDummy239 A), (nb090AlphaDummy240 h)),
        ((nb090AlphaDummy208 A), (nb090AlphaDummy210 h)), ((nb090AlphaDummy207 A),
        (nb090AlphaDummy209 h)), ((nb090AlphaDummy237 A), (nb090AlphaDummy238 h)),
        ((nb090AlphaDummy211 A), (nb090AlphaDummy212 h)), ((nb090AlphaDummy051 A),
        (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A),
        (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy222 A) ≠ (nb090AlphaDummy229 A) from (by
          unfold
            nb090AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0228
                    A)
                  0)))) (show (nb090AlphaDummy225 h) ≠ (nb090AlphaDummy230 h) from (by
          unfold
            nb090AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0229
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy222 A) ≠
        (nb090AlphaDummy227 A) from (by
          unfold
            nb090AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0226
                    A)
                  0)))) (show (nb090AlphaDummy225 h) ≠ (nb090AlphaDummy228 h) from (by
          unfold
            nb090AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0227
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy215
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy223 A) ≠ (nb090AlphaDummy229 A) from (by
          unfold
            nb090AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0232
                    A)
                  0)))) (show (nb090AlphaDummy226 h) ≠ (nb090AlphaDummy230 h) from (by
          unfold
            nb090AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0233
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy223 A) ≠
        (nb090AlphaDummy227 A) from (by
          unfold
            nb090AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0230
                    A)
                  0)))) (show (nb090AlphaDummy226 h) ≠ (nb090AlphaDummy228 h) from (by
          unfold
            nb090AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0231
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy222 A) ≠ (nb090AlphaDummy229 A) from (by
          unfold
            nb090AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0228
                    A)
                  0)))) (show (nb090AlphaDummy225 h) ≠ (nb090AlphaDummy230 h) from (by
          unfold
            nb090AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0229
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy222 A) ≠
        (nb090AlphaDummy227 A) from (by
          unfold
            nb090AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0226
                    A)
                  0)))) (show (nb090AlphaDummy225 h) ≠ (nb090AlphaDummy228 h) from (by
          unfold
            nb090AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0227
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy215
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy223 A) ≠ (nb090AlphaDummy229 A) from (by
          unfold
            nb090AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0232
                    A)
                  0)))) (show (nb090AlphaDummy226 h) ≠ (nb090AlphaDummy230 h) from (by
          unfold
            nb090AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0233
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy223 A) ≠
        (nb090AlphaDummy227 A) from (by
          unfold
            nb090AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0230
                    A)
                  0)))) (show (nb090AlphaDummy226 h) ≠ (nb090AlphaDummy228 h) from (by
          unfold
            nb090AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0231
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy223 A), (nb090AlphaDummy226 h)), ((nb090AlphaDummy222 A),
        (nb090AlphaDummy225 h)), ((nb090AlphaDummy221 A), (nb090AlphaDummy224 h)),
        ((nb090AlphaDummy219 A), (nb090AlphaDummy220 h)), ((nb090AlphaDummy215 A),
        (nb090AlphaDummy217 h)), ((nb090AlphaDummy216 A), (nb090AlphaDummy218 h)),
        ((nb090AlphaDummy241 A), (nb090AlphaDummy242 h)), ((nb090AlphaDummy239 A),
        (nb090AlphaDummy240 h)), ((nb090AlphaDummy208 A), (nb090AlphaDummy210 h)),
        ((nb090AlphaDummy207 A), (nb090AlphaDummy209 h)), ((nb090AlphaDummy237 A),
        (nb090AlphaDummy238 h)), ((nb090AlphaDummy211 A), (nb090AlphaDummy212 h)),
        ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A),
        (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A),
        (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy215 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy217 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy215 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy222 A) ≠ (nb090AlphaDummy233 A) from (by
          unfold
            nb090AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0236
                    A)
                  0)))) (show (nb090AlphaDummy225 h) ≠ (nb090AlphaDummy234 h) from (by
          unfold
            nb090AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0237
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy222 A) ≠
        (nb090AlphaDummy231 A) from (by
          unfold
            nb090AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0234
                    A)
                  0)))) (show (nb090AlphaDummy225 h) ≠ (nb090AlphaDummy232 h) from (by
          unfold
            nb090AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0235
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy215
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy222 A) ≠ (nb090AlphaDummy233 A) from (by
          unfold
            nb090AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0236
                    A)
                  0)))) (show (nb090AlphaDummy225 h) ≠ (nb090AlphaDummy234 h) from (by
          unfold
            nb090AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0237
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy222 A) ≠
        (nb090AlphaDummy231 A) from (by
          unfold
            nb090AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0234
                    A)
                  0)))) (show (nb090AlphaDummy225 h) ≠ (nb090AlphaDummy232 h) from (by
          unfold
            nb090AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0235
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy215
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy223 A) ≠ (nb090AlphaDummy235 A) from (by
          unfold
            nb090AlphaDummy235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0240
                    A)
                  0)))) (show (nb090AlphaDummy226 h) ≠ (nb090AlphaDummy236 h) from (by
          unfold
            nb090AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0241
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy223 A) ≠
        (nb090AlphaDummy231 A) from (by
          unfold
            nb090AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0238
                    A)
                  0)))) (show (nb090AlphaDummy226 h) ≠ (nb090AlphaDummy232 h) from (by
          unfold
            nb090AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0239
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy223 A) ≠ (nb090AlphaDummy235 A) from (by
          unfold
            nb090AlphaDummy235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0240
                    A)
                  0)))) (show (nb090AlphaDummy226 h) ≠ (nb090AlphaDummy236 h) from (by
          unfold
            nb090AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0241
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy223 A) ≠
        (nb090AlphaDummy231 A) from (by
          unfold
            nb090AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0238
                    A)
                  0)))) (show (nb090AlphaDummy226 h) ≠ (nb090AlphaDummy232 h) from (by
          unfold
            nb090AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0239
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy219 A) from
                                (by
                                  unfold nb090AlphaDummy219;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0222 A) 0))))
                              (show (nb090AlphaDummy217 h) ≠ (nb090AlphaDummy220 h) from
                                (by
                                  unfold nb090AlphaDummy220;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0223 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy219 A), (nb090AlphaDummy220 h)),
                              ((nb090AlphaDummy215 A), (nb090AlphaDummy217 h)),
                              ((nb090AlphaDummy216 A), (nb090AlphaDummy218 h)),
                              ((nb090AlphaDummy241 A), (nb090AlphaDummy242 h)),
                              ((nb090AlphaDummy239 A), (nb090AlphaDummy240 h)),
                              ((nb090AlphaDummy208 A), (nb090AlphaDummy210 h)),
                              ((nb090AlphaDummy207 A), (nb090AlphaDummy209 h)),
                              ((nb090AlphaDummy237 A), (nb090AlphaDummy238 h)),
                              ((nb090AlphaDummy211 A), (nb090AlphaDummy212 h)),
                              ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                              ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                              ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                              ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                              ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                              ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy219 A) from (by
                                unfold nb090AlphaDummy219;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0222 A) 0))))
                            (show (nb090AlphaDummy217 h) ≠ (nb090AlphaDummy220 h) from (by
                                unfold nb090AlphaDummy220;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0223 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy219 A) from
                                (by
                                  unfold nb090AlphaDummy219;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0222 A) 0))))
                              (show (nb090AlphaDummy217 h) ≠ (nb090AlphaDummy220 h) from
                                (by
                                  unfold nb090AlphaDummy220;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0223 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy219 A), (nb090AlphaDummy220 h)),
                              ((nb090AlphaDummy215 A), (nb090AlphaDummy217 h)),
                              ((nb090AlphaDummy216 A), (nb090AlphaDummy218 h)),
                              ((nb090AlphaDummy241 A), (nb090AlphaDummy242 h)),
                              ((nb090AlphaDummy239 A), (nb090AlphaDummy240 h)),
                              ((nb090AlphaDummy208 A), (nb090AlphaDummy210 h)),
                              ((nb090AlphaDummy207 A), (nb090AlphaDummy209 h)),
                              ((nb090AlphaDummy237 A), (nb090AlphaDummy238 h)),
                              ((nb090AlphaDummy211 A), (nb090AlphaDummy212 h)),
                              ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                              ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                              ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                              ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                              ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                              ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part035`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0011`. -/
@[expose]
noncomputable def nb090SplitAlpha0011 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classEq (Class.cv (nb090AlphaDummy055 A))
          (synCop (Class.cv (nb090AlphaDummy049 A)) (Class.cv (nb090AlphaDummy050 A))))
        (Wff.neg (synWex (nb090AlphaDummy051 A) (synWa
              (synWbr (Class.cv (nb090AlphaDummy049 A))
                (synCcnv (Class.cv (nb090AlphaDummy000 A)))
                (Class.cv (nb090AlphaDummy051 A)))
              (synWbr (Class.cv (nb090AlphaDummy051 A)) (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy050 A)))))))
      (Wff.imp (Wff.classEq (Class.cv (nb090AlphaDummy056 h))
          (synCop (Class.cv (nb090AlphaDummy052 h)) (Class.cv (nb090AlphaDummy053 h))))
        (Wff.neg (synWex (nb090AlphaDummy054 h) (synWa
              (synWbr (Class.cv (nb090AlphaDummy052 h)) (synCcnv (Class.cv h))
                (Class.cv (nb090AlphaDummy054 h)))
              (synWbr (Class.cv (nb090AlphaDummy054 h)) (Class.cv h)
                (Class.cv (nb090AlphaDummy053 h))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy055 A) from (by
                unfold nb090AlphaDummy055;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0044 A) 0)))))
          (Ne.symm (show (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy056 h) from (by
                unfold nb090AlphaDummy056;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0045 h) 0)))))
          (TAlphaVar.there (Ne.symm
              (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy055 A) from (by
                  unfold nb090AlphaDummy055;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0042 A) 0)))))
            (Ne.symm (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy056 h) from (by
                  unfold nb090AlphaDummy056;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0043 h) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0001 v u A h)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy058 A) from
                                    (by
                                      unfold nb090AlphaDummy058;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0074 A)
                                              1)))) (show
                                    (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy060 h) from
                                    (by
                                      unfold nb090AlphaDummy060;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0076 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy057 A) from
                                      (by
                                        unfold nb090AlphaDummy057;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0074 A)
                                                0)))) (show (nb090AlphaDummy053 h) ≠
                                        (nb090AlphaDummy059 h) from (by
                                        unfold nb090AlphaDummy059;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0076 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy087 A)
                                        from (by
                                          unfold nb090AlphaDummy087;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0078 A) 0)))) (show
                                        (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy088 h)
                                        from (by
                                          unfold nb090AlphaDummy088;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0079 h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy050 A) ≠
        (nb090AlphaDummy061 A) from (by
          unfold nb090AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0075 A) 0)))) (show (nb090AlphaDummy053 h) ≠
        (nb090AlphaDummy062 h) from (by
          unfold nb090AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0077 h) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb090AlphaDummy049 A))).fv ∪
                                      ((Class.cv (nb090AlphaDummy050 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb090AlphaDummy052 h))).fv ∪
                                      ((Class.cv (nb090AlphaDummy053 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (nb090SplitAlpha0002 v u A h)
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy089 A),
        (nb090AlphaDummy090 h)), ((nb090AlphaDummy058 A), (nb090AlphaDummy060 h)),
        ((nb090AlphaDummy057 A), (nb090AlphaDummy059 h)), ((nb090AlphaDummy087 A),
        (nb090AlphaDummy088 h)), ((nb090AlphaDummy061 A), (nb090AlphaDummy062 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A),
        (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synCcompl (synCsn (synC0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c])))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy058 A) from
                                    (by
                                      unfold nb090AlphaDummy058;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0074 A)
                                              1)))) (show
                                    (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy060 h) from
                                    (by
                                      unfold nb090AlphaDummy060;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0076 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy057 A) from
                                      (by
                                        unfold nb090AlphaDummy057;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0074 A)
                                                0)))) (show (nb090AlphaDummy053 h) ≠
                                        (nb090AlphaDummy059 h) from (by
                                        unfold nb090AlphaDummy059;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0076 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy087 A)
                                        from (by
                                          unfold nb090AlphaDummy087;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0078 A) 0)))) (show
                                        (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy088 h)
                                        from (by
                                          unfold nb090AlphaDummy088;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0079 h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy050 A) ≠
        (nb090AlphaDummy061 A) from (by
          unfold nb090AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0075 A) 0)))) (show (nb090AlphaDummy053 h) ≠
        (nb090AlphaDummy062 h) from (by
          unfold nb090AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0077 h) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb090AlphaDummy049 A))).fv ∪
                                      ((Class.cv (nb090AlphaDummy050 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb090AlphaDummy052 h))).fv ∪
                                      ((Class.cv (nb090AlphaDummy053 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (nb090SplitAlpha0002 v u A h)
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy089 A),
        (nb090AlphaDummy090 h)), ((nb090AlphaDummy058 A), (nb090AlphaDummy060 h)),
        ((nb090AlphaDummy057 A), (nb090AlphaDummy059 h)), ((nb090AlphaDummy087 A),
        (nb090AlphaDummy088 h)), ((nb090AlphaDummy061 A), (nb090AlphaDummy062 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A),
        (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synCcompl (synCsn (synC0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0003 v u A h)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090AlphaDummy051 A) ≠
        (nb090AlphaDummy094 A) from (by
          unfold nb090AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0112 A) 1)))) (show (nb090AlphaDummy054 h) ≠
        (nb090AlphaDummy096 h) from (by
          unfold nb090AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0114 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy093 A) from (by
          unfold nb090AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0112 A) 0)))) (show (nb090AlphaDummy054 h) ≠
        (nb090AlphaDummy095 h) from (by
          unfold nb090AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0114 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy123 A) from (by
          unfold nb090AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0116 A) 0)))) (show (nb090AlphaDummy054 h) ≠
        (nb090AlphaDummy124 h) from (by
          unfold nb090AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0117 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy097 A) from (by
          unfold nb090AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0113 A) 0)))) (show (nb090AlphaDummy054 h) ≠
        (nb090AlphaDummy098 h) from (by
          unfold nb090AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0115 h) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb090AlphaDummy049 A))).fv ∪ ((Class.cv (nb090AlphaDummy051 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy052 h))).fv ∪
        ((Class.cv (nb090AlphaDummy054 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0004 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy125 A), (nb090AlphaDummy126 h)), ((nb090AlphaDummy094 A),
        (nb090AlphaDummy096 h)), ((nb090AlphaDummy093 A), (nb090AlphaDummy095 h)),
        ((nb090AlphaDummy123 A), (nb090AlphaDummy124 h)), ((nb090AlphaDummy097 A),
        (nb090AlphaDummy098 h)), ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A),
        (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090AlphaDummy051 A) ≠
        (nb090AlphaDummy094 A) from (by
          unfold nb090AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0112 A) 1)))) (show (nb090AlphaDummy054 h) ≠
        (nb090AlphaDummy096 h) from (by
          unfold nb090AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0114 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy093 A) from (by
          unfold nb090AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0112 A) 0)))) (show (nb090AlphaDummy054 h) ≠
        (nb090AlphaDummy095 h) from (by
          unfold nb090AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0114 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy123 A) from (by
          unfold nb090AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0116 A) 0)))) (show (nb090AlphaDummy054 h) ≠
        (nb090AlphaDummy124 h) from (by
          unfold nb090AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0117 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy097 A) from (by
          unfold nb090AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0113 A) 0)))) (show (nb090AlphaDummy054 h) ≠
        (nb090AlphaDummy098 h) from (by
          unfold nb090AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0115 h) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb090AlphaDummy049 A))).fv ∪ ((Class.cv (nb090AlphaDummy051 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy052 h))).fv ∪
        ((Class.cv (nb090AlphaDummy054 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0004 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy125 A), (nb090AlphaDummy126 h)), ((nb090AlphaDummy094 A),
        (nb090AlphaDummy096 h)), ((nb090AlphaDummy093 A), (nb090AlphaDummy095 h)),
        ((nb090AlphaDummy123 A), (nb090AlphaDummy124 h)), ((nb090AlphaDummy097 A),
        (nb090AlphaDummy098 h)), ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A),
        (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                            (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy133 A) from (by
                                unfold nb090AlphaDummy133;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0124 A) 0)))))
                          (Ne.symm (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy134 h)
                              from (by
                                unfold nb090AlphaDummy134;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0125 h) 0)))))
                          (TAlphaVar.there (Ne.symm
                              (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy133 A) from
                                (by
                                  unfold nb090AlphaDummy133;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0122 A) 0)))))
                            (Ne.symm (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy134 h)
                                from (by
                                  unfold nb090AlphaDummy134;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0123 h) 0)))))
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb090SplitAlpha0005 v u A h)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy136 A) from (by
          unfold nb090AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154 A)
                  1)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy138 h) from (by
          unfold nb090AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156 h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy135 A) from (by
          unfold nb090AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154 A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy137 h) from (by
          unfold nb090AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy165 A) from (by
          unfold nb090AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0158
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy166 h) from (by
          unfold nb090AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0159
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy139 A) from (by
          unfold nb090AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0155
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy140 h) from (by
          unfold nb090AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0157
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy129 A))).fv ∪
        ((Class.cv (nb090AlphaDummy130 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy131 h))).fv ∪ ((Class.cv (nb090AlphaDummy132 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0006 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A),
        (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
        ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A),
        (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A),
        (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy136 A) from (by
          unfold nb090AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154 A)
                  1)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy138 h) from (by
          unfold nb090AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156 h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy135 A) from (by
          unfold nb090AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154 A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy137 h) from (by
          unfold nb090AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy165 A) from (by
          unfold nb090AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0158
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy166 h) from (by
          unfold nb090AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0159
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy139 A) from (by
          unfold nb090AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0155
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy140 h) from (by
          unfold nb090AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0157
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy129 A))).fv ∪
        ((Class.cv (nb090AlphaDummy130 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy131 h))).fv ∪ ((Class.cv (nb090AlphaDummy132 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0006 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A),
        (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
        ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A),
        (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A),
        (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb090SplitAlpha0007 v u A h)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy172 A) from (by
          unfold nb090AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192 A)
                  1)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy174 h) from (by
          unfold nb090AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194 h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy171 A) from (by
          unfold nb090AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192 A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy173 h) from (by
          unfold nb090AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy201 A) from (by
          unfold nb090AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0196
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy202 h) from (by
          unfold nb090AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0197
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy175 A) from (by
          unfold nb090AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0193
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy176 h) from (by
          unfold nb090AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0195
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy000
        A))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy130 A))).fv ∪ ((Class.cv
        (nb090AlphaDummy129 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy132 h))).fv ∪ ((Class.cv (nb090AlphaDummy131 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0008 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)), ((nb090AlphaDummy172 A),
        (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
        ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)), ((nb090AlphaDummy175 A),
        (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A),
        (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy172 A) from (by
          unfold nb090AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192 A)
                  1)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy174 h) from (by
          unfold nb090AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194 h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy171 A) from (by
          unfold nb090AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192 A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy173 h) from (by
          unfold nb090AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy201 A) from (by
          unfold nb090AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0196
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy202 h) from (by
          unfold nb090AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0197
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy175 A) from (by
          unfold nb090AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0193
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy176 h) from (by
          unfold nb090AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0195
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy000
        A))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy130 A))).fv ∪ ((Class.cv
        (nb090AlphaDummy129 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy132 h))).fv ∪ ((Class.cv (nb090AlphaDummy131 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0008 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)), ((nb090AlphaDummy172 A),
        (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
        ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)), ((nb090AlphaDummy175 A),
        (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A),
        (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                          (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy130 A) from (by
                              unfold nb090AlphaDummy130;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0212 A) 1))))
                          (show h ≠ (nb090AlphaDummy132 h) from (by
                              unfold nb090AlphaDummy132;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0213 h) 1))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy129 A) from (by
                                unfold nb090AlphaDummy129;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0212 A) 0))))
                            (show h ≠ (nb090AlphaDummy131 h) from (by
                                unfold nb090AlphaDummy131;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0213 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy133 A) from
                                (by
                                  unfold nb090AlphaDummy133;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0210 A) 0))))
                              (show h ≠ (nb090AlphaDummy134 h) from (by
                                  unfold nb090AlphaDummy134;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0211 h) 0))))
                              (TAlphaVar.there (show
                                  (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy051 A) from (by
                                    unfold nb090AlphaDummy051;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0206 A)
                                            2)))) (show h ≠ (nb090AlphaDummy054 h) from (by
                                    unfold nb090AlphaDummy054;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0208 h)
                                            2)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy050 A) from
                                    (by
                                      unfold nb090AlphaDummy050;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0206 A)
                                              1)))) (show h ≠ (nb090AlphaDummy053 h) from (by
                                      unfold nb090AlphaDummy053;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0208 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy049 A) from
                                      (by
                                        unfold nb090AlphaDummy049;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0206 A)
                                                0)))) (show h ≠ (nb090AlphaDummy052 h) from
                                      (by
                                        unfold nb090AlphaDummy052;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0208 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy055 A)
                                        from (by
                                          unfold nb090AlphaDummy055;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0207 A) 0))))
                                      (show h ≠ (nb090AlphaDummy056 h) from (by
                                          unfold nb090AlphaDummy056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0209 h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy047 A) from (by
          unfold nb090AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0204 A) 0)))) (show h ≠ (nb090AlphaDummy048 h) from (by
          unfold nb090AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0205 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy045 A) from (by
          unfold nb090AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0202 A) 0)))) (show h ≠ (nb090AlphaDummy046 h) from (by
          unfold nb090AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0203 h) 0)))) (TAlphaVar.here _ _ _)))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0009 v u A h)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090AlphaDummy050 A) ≠
        (nb090AlphaDummy208 A) from (by
          unfold nb090AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0242 A) 1)))) (show (nb090AlphaDummy053 h) ≠
        (nb090AlphaDummy210 h) from (by
          unfold nb090AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0244 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy207 A) from (by
          unfold nb090AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0242 A) 0)))) (show (nb090AlphaDummy053 h) ≠
        (nb090AlphaDummy209 h) from (by
          unfold nb090AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0244 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy237 A) from (by
          unfold nb090AlphaDummy237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0246 A) 0)))) (show (nb090AlphaDummy053 h) ≠
        (nb090AlphaDummy238 h) from (by
          unfold nb090AlphaDummy238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0247 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy211 A) from (by
          unfold nb090AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0243 A) 0)))) (show (nb090AlphaDummy053 h) ≠
        (nb090AlphaDummy212 h) from (by
          unfold nb090AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0245 h) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((synCcnv (Class.cv
        (nb090AlphaDummy000 A)))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv ∪
        ((synCcnv (Class.cv h))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb090AlphaDummy051 A))).fv ∪ ((Class.cv (nb090AlphaDummy050 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy054 h))).fv ∪
        ((Class.cv (nb090AlphaDummy053 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0010 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy239 A), (nb090AlphaDummy240 h)), ((nb090AlphaDummy208 A),
        (nb090AlphaDummy210 h)), ((nb090AlphaDummy207 A), (nb090AlphaDummy209 h)),
        ((nb090AlphaDummy237 A), (nb090AlphaDummy238 h)), ((nb090AlphaDummy211 A),
        (nb090AlphaDummy212 h)), ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A),
        (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090AlphaDummy050 A) ≠
        (nb090AlphaDummy208 A) from (by
          unfold nb090AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0242 A) 1)))) (show (nb090AlphaDummy053 h) ≠
        (nb090AlphaDummy210 h) from (by
          unfold nb090AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0244 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy207 A) from (by
          unfold nb090AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0242 A) 0)))) (show (nb090AlphaDummy053 h) ≠
        (nb090AlphaDummy209 h) from (by
          unfold nb090AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0244 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy237 A) from (by
          unfold nb090AlphaDummy237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0246 A) 0)))) (show (nb090AlphaDummy053 h) ≠
        (nb090AlphaDummy238 h) from (by
          unfold nb090AlphaDummy238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0247 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy211 A) from (by
          unfold nb090AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0243 A) 0)))) (show (nb090AlphaDummy053 h) ≠
        (nb090AlphaDummy212 h) from (by
          unfold nb090AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0245 h) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((synCcnv (Class.cv
        (nb090AlphaDummy000 A)))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv ∪
        ((synCcnv (Class.cv h))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb090AlphaDummy051 A))).fv ∪ ((Class.cv (nb090AlphaDummy050 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy054 h))).fv ∪
        ((Class.cv (nb090AlphaDummy053 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0010 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy239 A), (nb090AlphaDummy240 h)), ((nb090AlphaDummy208 A),
        (nb090AlphaDummy210 h)), ((nb090AlphaDummy207 A), (nb090AlphaDummy209 h)),
        ((nb090AlphaDummy237 A), (nb090AlphaDummy238 h)), ((nb090AlphaDummy211 A),
        (nb090AlphaDummy212 h)), ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A),
        (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy051 A) from (by
                    unfold nb090AlphaDummy051;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0206 A) 2))))
                (show h ≠ (nb090AlphaDummy054 h) from (by
                    unfold nb090AlphaDummy054;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0208 h) 2))))
                (TAlphaVar.there
                  (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy050 A) from (by
                      unfold nb090AlphaDummy050;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0206 A) 1))))
                  (show h ≠ (nb090AlphaDummy053 h) from (by
                      unfold nb090AlphaDummy053;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0208 h) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy049 A) from (by
                        unfold nb090AlphaDummy049;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0206 A) 0))))
                    (show h ≠ (nb090AlphaDummy052 h) from (by
                        unfold nb090AlphaDummy052;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0208 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy055 A) from (by
                          unfold nb090AlphaDummy055;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0207 A) 0))))
                      (show h ≠ (nb090AlphaDummy056 h) from (by
                          unfold nb090AlphaDummy056;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0209 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy047 A) from (by
                            unfold nb090AlphaDummy047;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0204 A) 0))))
                        (show h ≠ (nb090AlphaDummy048 h) from (by
                            unfold nb090AlphaDummy048;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0205 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy045 A) from (by
                              unfold nb090AlphaDummy045;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0202 A) 0))))
                          (show h ≠ (nb090AlphaDummy046 h) from (by
                              unfold nb090AlphaDummy046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0203 h) 0))))
                          (TAlphaVar.here _ _ _)))))))))))))

theorem nb090_wpp_notmem_0602 (A : Class) : (nb090AlphaDummy047 A) ∉ ((synCid)).fv :=
  by simpa only [nb090AlphaDummy047, fv_syn_cid] using (nb090_compact_fv_empty_0058 A)

theorem nb090_wpp_notmem_0603 (h : Var) : (nb090AlphaDummy048 h) ∉ ((synCid)).fv := by
  simpa only [nb090AlphaDummy048, fv_syn_cid] using (nb090_compact_fv_empty_0059 h)

theorem nb090_wpp_notmem_0604 (A : Class) : (nb090AlphaDummy045 A) ∉ ((synCid)).fv :=
  by simpa only [nb090AlphaDummy045, fv_syn_cid] using (nb090_compact_fv_empty_0060 A)

theorem nb090_wpp_notmem_0605 (h : Var) : (nb090AlphaDummy046 h) ∉ ((synCid)).fv := by
  simpa only [nb090AlphaDummy046, fv_syn_cid] using (nb090_compact_fv_empty_0061 h)

theorem nb090_wpp_notmem_0606 (A : Class) : (nb090AlphaDummy000 A) ∉ ((synCid)).fv :=
  by simpa only [nb090AlphaDummy000, fv_syn_cid] using (nb090_compact_fv_empty_0062 A)

theorem nb090_wpp_notmem_0607 (h : Var) : h ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb090_compact_fv_empty_0063 h)

theorem nb090_wpp_notmem_0608 (A : Class) : (nb090AlphaDummy002 A) ∉ ((synCid)).fv :=
  by simpa only [nb090AlphaDummy002, fv_syn_cid] using (nb090_compact_fv_empty_0020 A)

theorem nb090_wpp_notmem_0609 (v : Var) : v ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb090_compact_fv_empty_0021 v)

theorem nb090_wpp_notmem_0610 (A : Class) : (nb090AlphaDummy001 A) ∉ ((synCid)).fv :=
  by simpa only [nb090AlphaDummy001, fv_syn_cid] using (nb090_compact_fv_empty_0022 A)

theorem nb090_wpp_notmem_0611 (u : Var) : u ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb090_compact_fv_empty_0023 u)

theorem nb090_wpp_notmem_0612 (A : Class) : (nb090AlphaDummy003 A) ∉ ((synCid)).fv :=
  by simpa only [nb090AlphaDummy003, fv_syn_cid] using (nb090_compact_fv_empty_0024 A)

theorem nb090_wpp_notmem_0613 (v : Var) (u : Var) (A : Class) (h : Var) :
    (nb090AlphaDummy004 v u A h) ∉ ((synCid)).fv := by
  simpa only [nb090AlphaDummy004, fv_syn_cid] using
    (nb090_compact_fv_empty_0025 v u A h)

theorem nb090_compact_envfresh_0043 (v : Var) (u : Var) (A : Class) (h : Var) :
    TEnvFresh
      [((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      ((synCid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb090AlphaDummy047 A) (nb090AlphaDummy048 h)
      (nb090_wpp_notmem_0602 A) (nb090_wpp_notmem_0603 h)
      (TEnvFresh.consFresh (nb090AlphaDummy045 A) (nb090AlphaDummy046 h)
        (nb090_wpp_notmem_0604 A) (nb090_wpp_notmem_0605 h)
        (TEnvFresh.consFresh (nb090AlphaDummy000 A) h (nb090_wpp_notmem_0606 A)
          (nb090_wpp_notmem_0607 h)
          (TEnvFresh.consFresh (nb090AlphaDummy002 A) v (nb090_wpp_notmem_0608 A)
            (nb090_wpp_notmem_0609 v)
            (TEnvFresh.consFresh (nb090AlphaDummy001 A) u (nb090_wpp_notmem_0610 A)
              (nb090_wpp_notmem_0611 u) (TEnvFresh.consFresh (nb090AlphaDummy003 A)
                (nb090AlphaDummy004 v u A h) (nb090_wpp_notmem_0612 A)
                (nb090_wpp_notmem_0613 v u A h) (TEnvFresh.nil ((synCid)).fv)))))))

/-- Checked nominal proof certificate identified upstream as `nb090_wpp_refl_0043`. -/
@[expose]
noncomputable def nb090WppRefl0043 (v : Var) (u : Var) (A : Class) (h : Var) :
    TReflOn
      [((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      ((synCid)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0043 v u A h)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
