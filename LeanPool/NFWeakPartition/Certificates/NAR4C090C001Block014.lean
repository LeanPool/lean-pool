/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block013

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part045`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0021`. -/
@[expose]
noncomputable def nb090SplitAlpha0021 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy239 A), (nb090AlphaDummy240 h)),
        ((nb090AlphaDummy208 A), (nb090AlphaDummy210 h)),
        ((nb090AlphaDummy207 A), (nb090AlphaDummy209 h)),
        ((nb090AlphaDummy237 A), (nb090AlphaDummy238 h)),
        ((nb090AlphaDummy211 A), (nb090AlphaDummy212 h)),
        ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy239 A))
          (synCcompl (synCphi (Class.cv (nb090AlphaDummy208 A))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy239 A)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy240 h))
          (synCcompl (synCphi (Class.cv (nb090AlphaDummy210 h))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy240 h))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
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
                                    (mem_lt_freshVar (nb090_support_mem_0221 h) 0))))
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
                                      (mem_lt_freshVar (nb090_support_mem_0221 h) 1))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy208 A) ≠ (nb090AlphaDummy241 A) from
                                (by
                                  unfold nb090AlphaDummy241;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0250 A) 0))))
                              (show (nb090AlphaDummy210 h) ≠ (nb090AlphaDummy242 h) from
                                (by
                                  unfold nb090AlphaDummy242;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0251 h) 0))))
                              (TAlphaVar.there (show
                                  (nb090AlphaDummy208 A) ≠ (nb090AlphaDummy239 A) from (by
                                    unfold nb090AlphaDummy239;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0248 A)
                                            0)))) (show
                                  (nb090AlphaDummy210 h) ≠ (nb090AlphaDummy240 h) from (by
                                    unfold nb090AlphaDummy240;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0249 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy208 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy210 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy222 A) from (by
          unfold nb090AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0224 A) 1)))) (show (nb090AlphaDummy217 h) ≠
        (nb090AlphaDummy225 h) from (by
          unfold nb090AlphaDummy225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0225 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy221 A) from (by
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
                  (nb090_support_mem_0222 A)
                  0)))) (show (nb090AlphaDummy217 h) ≠ (nb090AlphaDummy220 h) from (by
          unfold nb090AlphaDummy220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0223 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
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
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy215 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy215 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy217 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy222
        A) ≠ (nb090AlphaDummy233 A) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy223
        A) ≠ (nb090AlphaDummy235 A) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy223
        A) ≠ (nb090AlphaDummy235 A) from (by
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
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy219 A) from
                                      (by
                                        unfold nb090AlphaDummy219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0222 A)
                                                0)))) (show (nb090AlphaDummy217 h) ≠
                                        (nb090AlphaDummy220 h) from (by
                                        unfold nb090AlphaDummy220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0223 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
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
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy219 A) from
                                    (by
                                      unfold nb090AlphaDummy219;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0222 A)
                                              0)))) (show
                                    (nb090AlphaDummy217 h) ≠ (nb090AlphaDummy220 h) from
                                    (by
                                      unfold nb090AlphaDummy220;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0223 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy219 A) from
                                      (by
                                        unfold nb090AlphaDummy219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0222 A)
                                                0)))) (show (nb090AlphaDummy217 h) ≠
                                        (nb090AlphaDummy220 h) from (by
                                        unfold nb090AlphaDummy220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0223 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
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
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
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
                                    (mem_lt_freshVar (nb090_support_mem_0221 h) 0))))
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
                                      (mem_lt_freshVar (nb090_support_mem_0221 h) 1))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy208 A) ≠ (nb090AlphaDummy241 A) from
                                (by
                                  unfold nb090AlphaDummy241;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0250 A) 0))))
                              (show (nb090AlphaDummy210 h) ≠ (nb090AlphaDummy242 h) from
                                (by
                                  unfold nb090AlphaDummy242;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0251 h) 0))))
                              (TAlphaVar.there (show
                                  (nb090AlphaDummy208 A) ≠ (nb090AlphaDummy239 A) from (by
                                    unfold nb090AlphaDummy239;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0248 A)
                                            0)))) (show
                                  (nb090AlphaDummy210 h) ≠ (nb090AlphaDummy240 h) from (by
                                    unfold nb090AlphaDummy240;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0249 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy208 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy210 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy222 A) from (by
          unfold nb090AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0224 A) 1)))) (show (nb090AlphaDummy217 h) ≠
        (nb090AlphaDummy225 h) from (by
          unfold nb090AlphaDummy225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0225 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy221 A) from (by
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
                  (nb090_support_mem_0222 A)
                  0)))) (show (nb090AlphaDummy217 h) ≠ (nb090AlphaDummy220 h) from (by
          unfold nb090AlphaDummy220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0223 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
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
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy215 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy215 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy217 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy222
        A) ≠ (nb090AlphaDummy233 A) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy223
        A) ≠ (nb090AlphaDummy235 A) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy223
        A) ≠ (nb090AlphaDummy235 A) from (by
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
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy219 A) from
                                      (by
                                        unfold nb090AlphaDummy219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0222 A)
                                                0)))) (show (nb090AlphaDummy217 h) ≠
                                        (nb090AlphaDummy220 h) from (by
                                        unfold nb090AlphaDummy220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0223 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
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
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy219 A) from
                                    (by
                                      unfold nb090AlphaDummy219;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0222 A)
                                              0)))) (show
                                    (nb090AlphaDummy217 h) ≠ (nb090AlphaDummy220 h) from
                                    (by
                                      unfold nb090AlphaDummy220;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0223 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy219 A) from
                                      (by
                                        unfold nb090AlphaDummy219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0222 A)
                                                0)))) (show (nb090AlphaDummy217 h) ≠
                                        (nb090AlphaDummy220 h) from (by
                                        unfold nb090AlphaDummy220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0223 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
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
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb090AlphaDummy239 A), (nb090AlphaDummy240 h)),
            ((nb090AlphaDummy208 A), (nb090AlphaDummy210 h)),
            ((nb090AlphaDummy207 A), (nb090AlphaDummy209 h)),
            ((nb090AlphaDummy237 A), (nb090AlphaDummy238 h)),
            ((nb090AlphaDummy211 A), (nb090AlphaDummy212 h)),
            ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
            ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
            ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
            ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
            ((nb090AlphaDummy001 A), u),
            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
          (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0022`. -/
@[expose]
noncomputable def nb090SplitAlpha0022 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.classEq (synCin (synCcom (Class.cv (nb090AlphaDummy000 A))
            (synCcnv (Class.cv (nb090AlphaDummy000 A)))) (synCid))
        (synCcom (Class.cv (nb090AlphaDummy000 A))
          (synCcnv (Class.cv (nb090AlphaDummy000 A)))))
      (Wff.classEq (synCin (synCcom (Class.cv h) (synCcnv (Class.cv h))) (synCid))
        (synCcom (Class.cv h) (synCcnv (Class.cv h)))) :=
  (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex
                        (TAlphaWff.ex (TAlphaWff.neg (nb090SplitAlpha0011 v u A h))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.reflOfReflOn
                      [((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                        ((nb090AlphaDummy001 A), u),
                        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                      (synCid) (nb090WppRefl0043 v u A h)))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex
                        (TAlphaWff.ex (TAlphaWff.neg (nb090SplitAlpha0011 v u A h))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.reflOfReflOn
                      [((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                        ((nb090AlphaDummy001 A), u),
                        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                      (synCid) (nb090WppRefl0043 v u A h)))))))))) (TAlphaClass.cab
      (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (Ne.symm
                    (show (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy055 A) from (by
                        unfold nb090AlphaDummy055;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0044 A) 0))))) (Ne.symm
                    (show (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy056 h) from (by
                        unfold nb090AlphaDummy056;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0045 h) 0)))))
                  (TAlphaVar.there (Ne.symm
                      (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy055 A) from (by
                          unfold nb090AlphaDummy055;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0042 A) 0))))) (Ne.symm
                      (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy056 h) from (by
                          unfold nb090AlphaDummy056;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0043 h) 0)))))
                    (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0012 v u A h)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090AlphaDummy050 A) ≠
        (nb090AlphaDummy058 A) from (by
          unfold nb090AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0074 A) 1)))) (show (nb090AlphaDummy053 h) ≠
        (nb090AlphaDummy060 h) from (by
          unfold nb090AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0076 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy057 A) from (by
          unfold nb090AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0074 A) 0)))) (show (nb090AlphaDummy053 h) ≠
        (nb090AlphaDummy059 h) from (by
          unfold nb090AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0076 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy087 A) from (by
          unfold nb090AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0078 A) 0)))) (show (nb090AlphaDummy053 h) ≠
        (nb090AlphaDummy088 h) from (by
          unfold nb090AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0079 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy061 A) from (by
          unfold nb090AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0075 A)
                  0)))) (show (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy062 h) from (by
          unfold nb090AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0077 h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy049 A))).fv ∪ ((Class.cv (nb090AlphaDummy050 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy052 h))).fv ∪
        ((Class.cv (nb090AlphaDummy053 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (nb090SplitAlpha0013 v u A h)))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090AlphaDummy050 A) ≠
        (nb090AlphaDummy058 A) from (by
          unfold nb090AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0074 A) 1)))) (show (nb090AlphaDummy053 h) ≠
        (nb090AlphaDummy060 h) from (by
          unfold nb090AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0076 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy057 A) from (by
          unfold nb090AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0074 A) 0)))) (show (nb090AlphaDummy053 h) ≠
        (nb090AlphaDummy059 h) from (by
          unfold nb090AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0076 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy087 A) from (by
          unfold nb090AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0078 A) 0)))) (show (nb090AlphaDummy053 h) ≠
        (nb090AlphaDummy088 h) from (by
          unfold nb090AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0079 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy061 A) from (by
          unfold nb090AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0075 A)
                  0)))) (show (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy062 h) from (by
          unfold nb090AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0077 h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy049 A))).fv ∪ ((Class.cv (nb090AlphaDummy050 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy052 h))).fv ∪
        ((Class.cv (nb090AlphaDummy053 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab
                                        (nb090SplitAlpha0013 v u A h)))))))))))))))
            (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb090SplitAlpha0014 v u A h)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy094 A) from (by
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
                  (nb090_support_mem_0112 A)
                  0)))) (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy095 h) from (by
          unfold nb090AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0114 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy051 A) ≠
        (nb090AlphaDummy123 A) from (by
          unfold nb090AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0116 A)
                  0)))) (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy124 h) from (by
          unfold nb090AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0117 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy051 A) ≠
        (nb090AlphaDummy097 A) from (by
          unfold nb090AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0113 A)
                  0)))) (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy098 h) from (by
          unfold nb090AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0115 h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy049 A))).fv ∪
        ((Class.cv (nb090AlphaDummy051 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy052 h))).fv ∪ ((Class.cv (nb090AlphaDummy054 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0015 v u A h))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy094 A) from (by
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
                  (nb090_support_mem_0112 A)
                  0)))) (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy095 h) from (by
          unfold nb090AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0114 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy051 A) ≠
        (nb090AlphaDummy123 A) from (by
          unfold nb090AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0116 A)
                  0)))) (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy124 h) from (by
          unfold nb090AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0117 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy051 A) ≠
        (nb090AlphaDummy097 A) from (by
          unfold nb090AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0113 A)
                  0)))) (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy098 h) from (by
          unfold nb090AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0115 h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy049 A))).fv ∪
        ((Class.cv (nb090AlphaDummy051 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy052 h))).fv ∪ ((Class.cv (nb090AlphaDummy054 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0015 v u A h)))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex
                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                              (TAlphaVar.there (Ne.symm (show
                                    (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy133 A) from
                                    (by
                                      unfold nb090AlphaDummy133;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0124 A)
                                              0))))) (Ne.symm (show
                                    (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy134 h) from
                                    (by
                                      unfold nb090AlphaDummy134;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0125 h)
                                              0))))) (TAlphaVar.there (Ne.symm (show
                                      (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy133 A) from
                                      (by
                                        unfold nb090AlphaDummy133;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0122 A)
                                                0))))) (Ne.symm (show
                                      (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy134 h) from
                                      (by
                                        unfold nb090AlphaDummy134;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0123 h)
                                                0))))) (TAlphaVar.here _ _ _))))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0016 v u A h))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy136 A) from (by
          unfold nb090AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154
                    A)
                  1)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy138 h) from (by
          unfold nb090AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy135 A) from (by
          unfold
            nb090AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy137 h) from (by
          unfold
            nb090AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy165 A) from (by
          unfold
            nb090AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0158
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy166 h) from (by
          unfold
            nb090AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0159
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy139 A) from (by
          unfold
            nb090AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0155
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy140 h) from (by
          unfold
            nb090AlphaDummy140;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0017 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A),
        (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
        ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A),
        (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001
        A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCcompl
        (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy136 A) from (by
          unfold nb090AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154
                    A)
                  1)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy138 h) from (by
          unfold nb090AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy135 A) from (by
          unfold
            nb090AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy137 h) from (by
          unfold
            nb090AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy165 A) from (by
          unfold
            nb090AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0158
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy166 h) from (by
          unfold
            nb090AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0159
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy139 A) from (by
          unfold
            nb090AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0155
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy140 h) from (by
          unfold
            nb090AlphaDummy140;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0017 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A),
        (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
        ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A),
        (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001
        A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCcompl
        (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0018 v u A h))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy172 A) from (by
          unfold nb090AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192
                    A)
                  1)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy174 h) from (by
          unfold nb090AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy171 A) from (by
          unfold
            nb090AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy173 h) from (by
          unfold
            nb090AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy201 A) from (by
          unfold
            nb090AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0196
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy202 h) from (by
          unfold
            nb090AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0197
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy175 A) from (by
          unfold
            nb090AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0193
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy176 h) from (by
          unfold
            nb090AlphaDummy176;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0019 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)), ((nb090AlphaDummy172 A),
        (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
        ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)), ((nb090AlphaDummy175 A),
        (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001
        A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCcompl
        (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy172 A) from (by
          unfold nb090AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192
                    A)
                  1)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy174 h) from (by
          unfold nb090AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy171 A) from (by
          unfold
            nb090AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy173 h) from (by
          unfold
            nb090AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy201 A) from (by
          unfold
            nb090AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0196
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy202 h) from (by
          unfold
            nb090AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0197
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy175 A) from (by
          unfold
            nb090AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0193
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy176 h) from (by
          unfold
            nb090AlphaDummy176;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0019 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)), ((nb090AlphaDummy172 A),
        (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
        ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)), ((nb090AlphaDummy175 A),
        (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001
        A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCcompl
        (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy130 A) from (by
                                    unfold nb090AlphaDummy130;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0212 A)
                                            1)))) (show h ≠ (nb090AlphaDummy132 h) from (by
                                    unfold nb090AlphaDummy132;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0213 h)
                                            1)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy129 A) from
                                    (by
                                      unfold nb090AlphaDummy129;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0212 A)
                                              0)))) (show h ≠ (nb090AlphaDummy131 h) from (by
                                      unfold nb090AlphaDummy131;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0213 h)
                                              0)))) (TAlphaVar.there (show
                                      (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy133 A) from
                                      (by
                                        unfold nb090AlphaDummy133;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0210 A)
                                                0)))) (show h ≠ (nb090AlphaDummy134 h) from
                                      (by
                                        unfold nb090AlphaDummy134;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0211 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy051 A)
                                        from (by
                                          unfold nb090AlphaDummy051;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0206 A) 2))))
                                      (show h ≠ (nb090AlphaDummy054 h) from (by
                                          unfold nb090AlphaDummy054;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0208 h) 2))))
                                      (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy050 A) from (by
          unfold nb090AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0206 A) 1)))) (show h ≠ (nb090AlphaDummy053 h) from (by
          unfold nb090AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0208 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy049 A) from (by
          unfold nb090AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0206 A) 0)))) (show h ≠ (nb090AlphaDummy052 h) from (by
          unfold nb090AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0208 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy055 A) from (by
          unfold nb090AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0207 A) 0)))) (show h ≠ (nb090AlphaDummy056 h) from (by
          unfold nb090AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0209 h) 0)))) (TAlphaVar.here _ _ _)))))))))))))))
                (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb090SplitAlpha0020 v u A h)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy208 A) from (by
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
                  (nb090_support_mem_0242 A)
                  0)))) (show (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy209 h) from (by
          unfold nb090AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0244 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy050 A) ≠
        (nb090AlphaDummy237 A) from (by
          unfold nb090AlphaDummy237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0246 A)
                  0)))) (show (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy238 h) from (by
          unfold nb090AlphaDummy238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0247 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy050 A) ≠
        (nb090AlphaDummy211 A) from (by
          unfold nb090AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0243 A)
                  0)))) (show (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy212 h) from (by
          unfold nb090AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0245 h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy000
        A))).fv ∪ ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) (by decide))
        (freshVar_injective (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy051 A))).fv ∪ ((Class.cv
        (nb090AlphaDummy050 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy054 h))).fv ∪ ((Class.cv (nb090AlphaDummy053 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0021 v u A h))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy208 A) from (by
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
                  (nb090_support_mem_0242 A)
                  0)))) (show (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy209 h) from (by
          unfold nb090AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0244 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy050 A) ≠
        (nb090AlphaDummy237 A) from (by
          unfold nb090AlphaDummy237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0246 A)
                  0)))) (show (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy238 h) from (by
          unfold nb090AlphaDummy238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0247 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy050 A) ≠
        (nb090AlphaDummy211 A) from (by
          unfold nb090AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0243 A)
                  0)))) (show (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy212 h) from (by
          unfold nb090AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0245 h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy000
        A))).fv ∪ ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) (by decide))
        (freshVar_injective (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy051 A))).fv ∪ ((Class.cv
        (nb090AlphaDummy050 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy054 h))).fv ∪ ((Class.cv (nb090AlphaDummy053 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0021 v u A h)))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                      (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy051 A) from (by
                          unfold nb090AlphaDummy051;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0206 A) 2))))
                      (show h ≠ (nb090AlphaDummy054 h) from (by
                          unfold nb090AlphaDummy054;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0208 h) 2))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy050 A) from (by
                            unfold nb090AlphaDummy050;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0206 A) 1))))
                        (show h ≠ (nb090AlphaDummy053 h) from (by
                            unfold nb090AlphaDummy053;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0208 h) 1))))
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
                                    (mem_lt_freshVar (nb090_support_mem_0208 h) 0))))
                          (TAlphaVar.there
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
                            (TAlphaVar.here _ _ _))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part046`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0023`. -/
@[expose]
noncomputable def nb090SplitAlpha0023 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy251 A), (nb090AlphaDummy252 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
        ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.classMem (Class.cv (nb090AlphaDummy251 A)) (synCcompl
          (Class.cab (nb090AlphaDummy247 A)
            (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy244 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                (synCphi (Class.cv (nb090AlphaDummy248 A))))))))
      (Wff.classMem (Class.cv (nb090AlphaDummy252 h)) (synCcompl
          (Class.cab (nb090AlphaDummy249 h)
            (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy246 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                (synCphi (Class.cv (nb090AlphaDummy250 h)))))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb090AlphaDummy244 A) ≠ (nb090AlphaDummy248 A) from (by
                            unfold nb090AlphaDummy248;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0252 A) 1))))
                        (show (nb090AlphaDummy246 h) ≠ (nb090AlphaDummy250 h) from (by
                            unfold nb090AlphaDummy250;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0254 h) 1))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy244 A) ≠ (nb090AlphaDummy247 A) from (by
                              unfold nb090AlphaDummy247;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0252 A) 0))))
                          (show (nb090AlphaDummy246 h) ≠ (nb090AlphaDummy249 h) from (by
                              unfold nb090AlphaDummy249;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0254 h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy244 A) ≠ (nb090AlphaDummy253 A) from (by
                                unfold nb090AlphaDummy253;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0256 A) 0))))
                            (show (nb090AlphaDummy246 h) ≠ (nb090AlphaDummy254 h) from (by
                                unfold nb090AlphaDummy254;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0257 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy244 A) ≠ (nb090AlphaDummy251 A) from
                                (by
                                  unfold nb090AlphaDummy251;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0253 A) 0))))
                              (show (nb090AlphaDummy246 h) ≠ (nb090AlphaDummy252 h) from
                                (by
                                  unfold nb090AlphaDummy252;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0255 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb090AlphaDummy244 A))).fv ∪
                            ((Class.cv (nb090AlphaDummy243 A))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb090AlphaDummy246 h))).fv ∪
                            ((Class.cv (nb090AlphaDummy245 h))).fv) (by decide))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090AlphaDummy248 A) ≠ (nb090AlphaDummy255 A) from (by
                                    unfold nb090AlphaDummy255;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0258 A)
                                            0)))) (show
                                  (nb090AlphaDummy250 h) ≠ (nb090AlphaDummy257 h) from (by
                                    unfold nb090AlphaDummy257;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0259 h)
                                            0)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy248 A) ≠ (nb090AlphaDummy256 A) from
                                    (by
                                      unfold nb090AlphaDummy256;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0258 A)
                                              1)))) (show
                                    (nb090AlphaDummy250 h) ≠ (nb090AlphaDummy258 h) from
                                    (by
                                      unfold nb090AlphaDummy258;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0259 h)
                                              1)))) (TAlphaVar.here _ _ _)))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective
                                  (((Class.cv (nb090AlphaDummy248 A))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb090AlphaDummy250 h))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy255 A) ≠ (nb090AlphaDummy262 A) from (by
          unfold nb090AlphaDummy262;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0262 A)
                  1)))) (show (nb090AlphaDummy257 h) ≠ (nb090AlphaDummy265 h) from (by
          unfold nb090AlphaDummy265;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0263 h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy255 A) ≠
        (nb090AlphaDummy261 A) from (by
          unfold nb090AlphaDummy261;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0262 A)
                  0)))) (show (nb090AlphaDummy257 h) ≠ (nb090AlphaDummy264 h) from (by
          unfold nb090AlphaDummy264;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0263 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy255 A) ≠
        (nb090AlphaDummy259 A) from (by
          unfold nb090AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0260
                    A)
                  0)))) (show (nb090AlphaDummy257 h) ≠ (nb090AlphaDummy260 h) from (by
          unfold nb090AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0261
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy263 A), (nb090AlphaDummy266 h)), ((nb090AlphaDummy262 A),
        (nb090AlphaDummy265 h)), ((nb090AlphaDummy261 A), (nb090AlphaDummy264 h)),
        ((nb090AlphaDummy259 A), (nb090AlphaDummy260 h)), ((nb090AlphaDummy255 A),
        (nb090AlphaDummy257 h)), ((nb090AlphaDummy256 A), (nb090AlphaDummy258 h)),
        ((nb090AlphaDummy248 A), (nb090AlphaDummy250 h)), ((nb090AlphaDummy247 A),
        (nb090AlphaDummy249 h)), ((nb090AlphaDummy253 A), (nb090AlphaDummy254 h)),
        ((nb090AlphaDummy251 A), (nb090AlphaDummy252 h)), ((nb090AlphaDummy244 A),
        (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy262 A) ≠
        (nb090AlphaDummy269 A) from (by
          unfold
            nb090AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0266
                    A)
                  0)))) (show (nb090AlphaDummy265 h) ≠ (nb090AlphaDummy270 h) from (by
          unfold
            nb090AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0267
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy262 A) ≠
        (nb090AlphaDummy267 A) from (by
          unfold
            nb090AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0264
                    A)
                  0)))) (show (nb090AlphaDummy265 h) ≠ (nb090AlphaDummy268 h) from (by
          unfold
            nb090AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0265
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy255
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy263 A) ≠ (nb090AlphaDummy269 A) from (by
          unfold
            nb090AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0270
                    A)
                  0)))) (show (nb090AlphaDummy266 h) ≠ (nb090AlphaDummy270 h) from (by
          unfold
            nb090AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0271
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy263 A) ≠
        (nb090AlphaDummy267 A) from (by
          unfold
            nb090AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0268
                    A)
                  0)))) (show (nb090AlphaDummy266 h) ≠ (nb090AlphaDummy268 h) from (by
          unfold
            nb090AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0269
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy262 A) ≠ (nb090AlphaDummy269 A) from (by
          unfold
            nb090AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0266
                    A)
                  0)))) (show (nb090AlphaDummy265 h) ≠ (nb090AlphaDummy270 h) from (by
          unfold
            nb090AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0267
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy262 A) ≠
        (nb090AlphaDummy267 A) from (by
          unfold
            nb090AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0264
                    A)
                  0)))) (show (nb090AlphaDummy265 h) ≠ (nb090AlphaDummy268 h) from (by
          unfold
            nb090AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0265
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy255
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy263 A) ≠ (nb090AlphaDummy269 A) from (by
          unfold
            nb090AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0270
                    A)
                  0)))) (show (nb090AlphaDummy266 h) ≠ (nb090AlphaDummy270 h) from (by
          unfold
            nb090AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0271
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy263 A) ≠
        (nb090AlphaDummy267 A) from (by
          unfold
            nb090AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0268
                    A)
                  0)))) (show (nb090AlphaDummy266 h) ≠ (nb090AlphaDummy268 h) from (by
          unfold
            nb090AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0269
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy263 A), (nb090AlphaDummy266 h)), ((nb090AlphaDummy262 A),
        (nb090AlphaDummy265 h)), ((nb090AlphaDummy261 A), (nb090AlphaDummy264 h)),
        ((nb090AlphaDummy259 A), (nb090AlphaDummy260 h)), ((nb090AlphaDummy255 A),
        (nb090AlphaDummy257 h)), ((nb090AlphaDummy256 A), (nb090AlphaDummy258 h)),
        ((nb090AlphaDummy248 A), (nb090AlphaDummy250 h)), ((nb090AlphaDummy247 A),
        (nb090AlphaDummy249 h)), ((nb090AlphaDummy253 A), (nb090AlphaDummy254 h)),
        ((nb090AlphaDummy251 A), (nb090AlphaDummy252 h)), ((nb090AlphaDummy244 A),
        (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A
        h))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy255 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy257
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy255 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy262 A) ≠
        (nb090AlphaDummy273 A) from (by
          unfold
            nb090AlphaDummy273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0274
                    A)
                  0)))) (show (nb090AlphaDummy265 h) ≠ (nb090AlphaDummy274 h) from (by
          unfold
            nb090AlphaDummy274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0275
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy262 A) ≠
        (nb090AlphaDummy271 A) from (by
          unfold
            nb090AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0272
                    A)
                  0)))) (show (nb090AlphaDummy265 h) ≠ (nb090AlphaDummy272 h) from (by
          unfold
            nb090AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0273
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy255
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy262 A) ≠ (nb090AlphaDummy273 A) from (by
          unfold
            nb090AlphaDummy273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0274
                    A)
                  0)))) (show (nb090AlphaDummy265 h) ≠ (nb090AlphaDummy274 h) from (by
          unfold
            nb090AlphaDummy274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0275
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy262 A) ≠
        (nb090AlphaDummy271 A) from (by
          unfold
            nb090AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0272
                    A)
                  0)))) (show (nb090AlphaDummy265 h) ≠ (nb090AlphaDummy272 h) from (by
          unfold
            nb090AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0273
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy255
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy263 A) ≠
        (nb090AlphaDummy275 A) from (by
          unfold
            nb090AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0278
                    A)
                  0)))) (show (nb090AlphaDummy266 h) ≠ (nb090AlphaDummy276 h) from (by
          unfold
            nb090AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0279
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy263 A) ≠
        (nb090AlphaDummy271 A) from (by
          unfold
            nb090AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0276
                    A)
                  0)))) (show (nb090AlphaDummy266 h) ≠ (nb090AlphaDummy272 h) from (by
          unfold
            nb090AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0277
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy263
        A) ≠ (nb090AlphaDummy275 A) from (by
          unfold
            nb090AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0278
                    A)
                  0)))) (show (nb090AlphaDummy266 h) ≠ (nb090AlphaDummy276 h) from (by
          unfold
            nb090AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0279
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy263 A) ≠
        (nb090AlphaDummy271 A) from (by
          unfold
            nb090AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0276
                    A)
                  0)))) (show (nb090AlphaDummy266 h) ≠ (nb090AlphaDummy272 h) from (by
          unfold
            nb090AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0277
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy255 A) ≠ (nb090AlphaDummy259 A) from (by
          unfold nb090AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0260 A) 0)))) (show (nb090AlphaDummy257 h) ≠
        (nb090AlphaDummy260 h) from (by
          unfold nb090AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0261 h) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy259 A),
        (nb090AlphaDummy260 h)), ((nb090AlphaDummy255 A), (nb090AlphaDummy257 h)),
        ((nb090AlphaDummy256 A), (nb090AlphaDummy258 h)), ((nb090AlphaDummy248 A),
        (nb090AlphaDummy250 h)), ((nb090AlphaDummy247 A), (nb090AlphaDummy249 h)),
        ((nb090AlphaDummy253 A), (nb090AlphaDummy254 h)), ((nb090AlphaDummy251 A),
        (nb090AlphaDummy252 h)), ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
        ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synCnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090AlphaDummy255 A) ≠
        (nb090AlphaDummy259 A) from (by
          unfold nb090AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0260 A) 0)))) (show (nb090AlphaDummy257 h) ≠
        (nb090AlphaDummy260 h) from (by
          unfold nb090AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0261 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy255 A) ≠ (nb090AlphaDummy259 A) from (by
          unfold nb090AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0260 A) 0)))) (show (nb090AlphaDummy257 h) ≠
        (nb090AlphaDummy260 h) from (by
          unfold nb090AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0261 h) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy259 A),
        (nb090AlphaDummy260 h)), ((nb090AlphaDummy255 A), (nb090AlphaDummy257 h)),
        ((nb090AlphaDummy256 A), (nb090AlphaDummy258 h)), ((nb090AlphaDummy248 A),
        (nb090AlphaDummy250 h)), ((nb090AlphaDummy247 A), (nb090AlphaDummy249 h)),
        ((nb090AlphaDummy253 A), (nb090AlphaDummy254 h)), ((nb090AlphaDummy251 A),
        (nb090AlphaDummy252 h)), ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
        ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCnnc)
                                        (by simp only [fv_syn_cnnc]))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb090AlphaDummy244 A) ≠ (nb090AlphaDummy248 A) from (by
                            unfold nb090AlphaDummy248;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0252 A) 1))))
                        (show (nb090AlphaDummy246 h) ≠ (nb090AlphaDummy250 h) from (by
                            unfold nb090AlphaDummy250;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0254 h) 1))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy244 A) ≠ (nb090AlphaDummy247 A) from (by
                              unfold nb090AlphaDummy247;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0252 A) 0))))
                          (show (nb090AlphaDummy246 h) ≠ (nb090AlphaDummy249 h) from (by
                              unfold nb090AlphaDummy249;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0254 h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy244 A) ≠ (nb090AlphaDummy253 A) from (by
                                unfold nb090AlphaDummy253;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0256 A) 0))))
                            (show (nb090AlphaDummy246 h) ≠ (nb090AlphaDummy254 h) from (by
                                unfold nb090AlphaDummy254;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0257 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy244 A) ≠ (nb090AlphaDummy251 A) from
                                (by
                                  unfold nb090AlphaDummy251;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0253 A) 0))))
                              (show (nb090AlphaDummy246 h) ≠ (nb090AlphaDummy252 h) from
                                (by
                                  unfold nb090AlphaDummy252;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0255 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb090AlphaDummy244 A))).fv ∪
                            ((Class.cv (nb090AlphaDummy243 A))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb090AlphaDummy246 h))).fv ∪
                            ((Class.cv (nb090AlphaDummy245 h))).fv) (by decide))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090AlphaDummy248 A) ≠ (nb090AlphaDummy255 A) from (by
                                    unfold nb090AlphaDummy255;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0258 A)
                                            0)))) (show
                                  (nb090AlphaDummy250 h) ≠ (nb090AlphaDummy257 h) from (by
                                    unfold nb090AlphaDummy257;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0259 h)
                                            0)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy248 A) ≠ (nb090AlphaDummy256 A) from
                                    (by
                                      unfold nb090AlphaDummy256;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0258 A)
                                              1)))) (show
                                    (nb090AlphaDummy250 h) ≠ (nb090AlphaDummy258 h) from
                                    (by
                                      unfold nb090AlphaDummy258;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0259 h)
                                              1)))) (TAlphaVar.here _ _ _)))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective
                                  (((Class.cv (nb090AlphaDummy248 A))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb090AlphaDummy250 h))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy255 A) ≠ (nb090AlphaDummy262 A) from (by
          unfold nb090AlphaDummy262;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0262 A)
                  1)))) (show (nb090AlphaDummy257 h) ≠ (nb090AlphaDummy265 h) from (by
          unfold nb090AlphaDummy265;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0263 h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy255 A) ≠
        (nb090AlphaDummy261 A) from (by
          unfold nb090AlphaDummy261;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0262 A)
                  0)))) (show (nb090AlphaDummy257 h) ≠ (nb090AlphaDummy264 h) from (by
          unfold nb090AlphaDummy264;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0263 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy255 A) ≠
        (nb090AlphaDummy259 A) from (by
          unfold nb090AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0260
                    A)
                  0)))) (show (nb090AlphaDummy257 h) ≠ (nb090AlphaDummy260 h) from (by
          unfold nb090AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0261
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy263 A), (nb090AlphaDummy266 h)), ((nb090AlphaDummy262 A),
        (nb090AlphaDummy265 h)), ((nb090AlphaDummy261 A), (nb090AlphaDummy264 h)),
        ((nb090AlphaDummy259 A), (nb090AlphaDummy260 h)), ((nb090AlphaDummy255 A),
        (nb090AlphaDummy257 h)), ((nb090AlphaDummy256 A), (nb090AlphaDummy258 h)),
        ((nb090AlphaDummy248 A), (nb090AlphaDummy250 h)), ((nb090AlphaDummy247 A),
        (nb090AlphaDummy249 h)), ((nb090AlphaDummy253 A), (nb090AlphaDummy254 h)),
        ((nb090AlphaDummy251 A), (nb090AlphaDummy252 h)), ((nb090AlphaDummy244 A),
        (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy262 A) ≠
        (nb090AlphaDummy269 A) from (by
          unfold
            nb090AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0266
                    A)
                  0)))) (show (nb090AlphaDummy265 h) ≠ (nb090AlphaDummy270 h) from (by
          unfold
            nb090AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0267
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy262 A) ≠
        (nb090AlphaDummy267 A) from (by
          unfold
            nb090AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0264
                    A)
                  0)))) (show (nb090AlphaDummy265 h) ≠ (nb090AlphaDummy268 h) from (by
          unfold
            nb090AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0265
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy255
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy263 A) ≠ (nb090AlphaDummy269 A) from (by
          unfold
            nb090AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0270
                    A)
                  0)))) (show (nb090AlphaDummy266 h) ≠ (nb090AlphaDummy270 h) from (by
          unfold
            nb090AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0271
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy263 A) ≠
        (nb090AlphaDummy267 A) from (by
          unfold
            nb090AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0268
                    A)
                  0)))) (show (nb090AlphaDummy266 h) ≠ (nb090AlphaDummy268 h) from (by
          unfold
            nb090AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0269
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy262 A) ≠ (nb090AlphaDummy269 A) from (by
          unfold
            nb090AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0266
                    A)
                  0)))) (show (nb090AlphaDummy265 h) ≠ (nb090AlphaDummy270 h) from (by
          unfold
            nb090AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0267
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy262 A) ≠
        (nb090AlphaDummy267 A) from (by
          unfold
            nb090AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0264
                    A)
                  0)))) (show (nb090AlphaDummy265 h) ≠ (nb090AlphaDummy268 h) from (by
          unfold
            nb090AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0265
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy255
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy263 A) ≠ (nb090AlphaDummy269 A) from (by
          unfold
            nb090AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0270
                    A)
                  0)))) (show (nb090AlphaDummy266 h) ≠ (nb090AlphaDummy270 h) from (by
          unfold
            nb090AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0271
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy263 A) ≠
        (nb090AlphaDummy267 A) from (by
          unfold
            nb090AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0268
                    A)
                  0)))) (show (nb090AlphaDummy266 h) ≠ (nb090AlphaDummy268 h) from (by
          unfold
            nb090AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0269
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy263 A), (nb090AlphaDummy266 h)), ((nb090AlphaDummy262 A),
        (nb090AlphaDummy265 h)), ((nb090AlphaDummy261 A), (nb090AlphaDummy264 h)),
        ((nb090AlphaDummy259 A), (nb090AlphaDummy260 h)), ((nb090AlphaDummy255 A),
        (nb090AlphaDummy257 h)), ((nb090AlphaDummy256 A), (nb090AlphaDummy258 h)),
        ((nb090AlphaDummy248 A), (nb090AlphaDummy250 h)), ((nb090AlphaDummy247 A),
        (nb090AlphaDummy249 h)), ((nb090AlphaDummy253 A), (nb090AlphaDummy254 h)),
        ((nb090AlphaDummy251 A), (nb090AlphaDummy252 h)), ((nb090AlphaDummy244 A),
        (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A
        h))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy255 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy257
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy255 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy262 A) ≠
        (nb090AlphaDummy273 A) from (by
          unfold
            nb090AlphaDummy273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0274
                    A)
                  0)))) (show (nb090AlphaDummy265 h) ≠ (nb090AlphaDummy274 h) from (by
          unfold
            nb090AlphaDummy274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0275
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy262 A) ≠
        (nb090AlphaDummy271 A) from (by
          unfold
            nb090AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0272
                    A)
                  0)))) (show (nb090AlphaDummy265 h) ≠ (nb090AlphaDummy272 h) from (by
          unfold
            nb090AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0273
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy255
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy262 A) ≠ (nb090AlphaDummy273 A) from (by
          unfold
            nb090AlphaDummy273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0274
                    A)
                  0)))) (show (nb090AlphaDummy265 h) ≠ (nb090AlphaDummy274 h) from (by
          unfold
            nb090AlphaDummy274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0275
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy262 A) ≠
        (nb090AlphaDummy271 A) from (by
          unfold
            nb090AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0272
                    A)
                  0)))) (show (nb090AlphaDummy265 h) ≠ (nb090AlphaDummy272 h) from (by
          unfold
            nb090AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0273
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy255
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy263 A) ≠
        (nb090AlphaDummy275 A) from (by
          unfold
            nb090AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0278
                    A)
                  0)))) (show (nb090AlphaDummy266 h) ≠ (nb090AlphaDummy276 h) from (by
          unfold
            nb090AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0279
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy263 A) ≠
        (nb090AlphaDummy271 A) from (by
          unfold
            nb090AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0276
                    A)
                  0)))) (show (nb090AlphaDummy266 h) ≠ (nb090AlphaDummy272 h) from (by
          unfold
            nb090AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0277
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy263
        A) ≠ (nb090AlphaDummy275 A) from (by
          unfold
            nb090AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0278
                    A)
                  0)))) (show (nb090AlphaDummy266 h) ≠ (nb090AlphaDummy276 h) from (by
          unfold
            nb090AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0279
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy263 A) ≠
        (nb090AlphaDummy271 A) from (by
          unfold
            nb090AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0276
                    A)
                  0)))) (show (nb090AlphaDummy266 h) ≠ (nb090AlphaDummy272 h) from (by
          unfold
            nb090AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0277
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy255 A) ≠ (nb090AlphaDummy259 A) from (by
          unfold nb090AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0260 A) 0)))) (show (nb090AlphaDummy257 h) ≠
        (nb090AlphaDummy260 h) from (by
          unfold nb090AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0261 h) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy259 A),
        (nb090AlphaDummy260 h)), ((nb090AlphaDummy255 A), (nb090AlphaDummy257 h)),
        ((nb090AlphaDummy256 A), (nb090AlphaDummy258 h)), ((nb090AlphaDummy248 A),
        (nb090AlphaDummy250 h)), ((nb090AlphaDummy247 A), (nb090AlphaDummy249 h)),
        ((nb090AlphaDummy253 A), (nb090AlphaDummy254 h)), ((nb090AlphaDummy251 A),
        (nb090AlphaDummy252 h)), ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
        ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synCnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090AlphaDummy255 A) ≠
        (nb090AlphaDummy259 A) from (by
          unfold nb090AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0260 A) 0)))) (show (nb090AlphaDummy257 h) ≠
        (nb090AlphaDummy260 h) from (by
          unfold nb090AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0261 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy255 A) ≠ (nb090AlphaDummy259 A) from (by
          unfold nb090AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0260 A) 0)))) (show (nb090AlphaDummy257 h) ≠
        (nb090AlphaDummy260 h) from (by
          unfold nb090AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0261 h) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy259 A),
        (nb090AlphaDummy260 h)), ((nb090AlphaDummy255 A), (nb090AlphaDummy257 h)),
        ((nb090AlphaDummy256 A), (nb090AlphaDummy258 h)), ((nb090AlphaDummy248 A),
        (nb090AlphaDummy250 h)), ((nb090AlphaDummy247 A), (nb090AlphaDummy249 h)),
        ((nb090AlphaDummy253 A), (nb090AlphaDummy254 h)), ((nb090AlphaDummy251 A),
        (nb090AlphaDummy252 h)), ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
        ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCnnc)
                                        (by simp only [fv_syn_cnnc]))))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
