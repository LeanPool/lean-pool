/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block014

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part047`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0024`. -/
@[expose]
noncomputable def nb090SplitAlpha0024 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy248 A), (nb090AlphaDummy250 h)),
        ((nb090AlphaDummy247 A), (nb090AlphaDummy249 h)),
        ((nb090AlphaDummy277 A), (nb090AlphaDummy278 h)),
        ((nb090AlphaDummy251 A), (nb090AlphaDummy252 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
        ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy248 A))
          (Class.cv (nb090AlphaDummy243 A))) (Wff.neg
          (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
            (synCun (synCphi (Class.cv (nb090AlphaDummy248 A))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy250 h))
          (Class.cv (nb090AlphaDummy245 h))) (Wff.neg
          (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
            (synCun (synCphi (Class.cv (nb090AlphaDummy250 h))) (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy243 A) ≠ (nb090AlphaDummy248 A) from (by
              unfold nb090AlphaDummy248;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0280 A) 1))))
          (show (nb090AlphaDummy245 h) ≠ (nb090AlphaDummy250 h) from (by
              unfold nb090AlphaDummy250;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0282 h) 1))))
          (TAlphaVar.there (show (nb090AlphaDummy243 A) ≠ (nb090AlphaDummy247 A) from (by
                unfold nb090AlphaDummy247;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0280 A) 0))))
            (show (nb090AlphaDummy245 h) ≠ (nb090AlphaDummy249 h) from (by
                unfold nb090AlphaDummy249;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0282 h) 0))))
            (TAlphaVar.there (show (nb090AlphaDummy243 A) ≠ (nb090AlphaDummy277 A) from
                (by
                  unfold nb090AlphaDummy277;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0284 A) 0))))
              (show (nb090AlphaDummy245 h) ≠ (nb090AlphaDummy278 h) from (by
                  unfold nb090AlphaDummy278;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0285 h) 0))))
              (TAlphaVar.there (show (nb090AlphaDummy243 A) ≠ (nb090AlphaDummy251 A) from
                  (by
                    unfold nb090AlphaDummy251;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0281 A) 0))))
                (show (nb090AlphaDummy245 h) ≠ (nb090AlphaDummy252 h) from (by
                    unfold nb090AlphaDummy252;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0283 h) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪ ((synCvv)).fv)
                    (by decide))
                  (freshVar_injective (((synCcnv (Class.cv h))).fv ∪ ((synCvv)).fv)
                    (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb090AlphaDummy244 A))).fv ∪
                ((Class.cv (nb090AlphaDummy243 A))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb090AlphaDummy246 h))).fv ∪
                ((Class.cv (nb090AlphaDummy245 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy248 A) ≠ (nb090AlphaDummy255 A) from
                                      (by
                                        unfold nb090AlphaDummy255;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0258 A)
                                                0)))) (show (nb090AlphaDummy250 h) ≠
                                        (nb090AlphaDummy257 h) from (by
                                        unfold nb090AlphaDummy257;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0259 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy248 A) ≠ (nb090AlphaDummy256 A)
                                        from (by
                                          unfold nb090AlphaDummy256;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0258 A) 1)))) (show
                                        (nb090AlphaDummy250 h) ≠ (nb090AlphaDummy258 h)
                                        from (by
                                          unfold nb090AlphaDummy258;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0259 h) 1))))
                                      (TAlphaVar.there (show (nb090AlphaDummy248 A) ≠
        (nb090AlphaDummy281 A) from (by
          unfold nb090AlphaDummy281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0288 A) 0)))) (show (nb090AlphaDummy250 h) ≠
        (nb090AlphaDummy282 h) from (by
          unfold nb090AlphaDummy282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0289 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy248 A) ≠ (nb090AlphaDummy279 A) from (by
          unfold nb090AlphaDummy279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0286 A) 0)))) (show (nb090AlphaDummy250 h) ≠
        (nb090AlphaDummy280 h) from (by
          unfold nb090AlphaDummy280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0287 h) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb090AlphaDummy248 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb090AlphaDummy250 h))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy255 A) ≠ (nb090AlphaDummy262 A) from (by
          unfold nb090AlphaDummy262;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0262
                    A)
                  1)))) (show (nb090AlphaDummy257 h) ≠ (nb090AlphaDummy265 h) from (by
          unfold nb090AlphaDummy265;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0263
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy255 A) ≠
        (nb090AlphaDummy261 A) from (by
          unfold nb090AlphaDummy261;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0262
                    A)
                  0)))) (show (nb090AlphaDummy257 h) ≠ (nb090AlphaDummy264 h) from (by
          unfold nb090AlphaDummy264;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0263
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy255 A) ≠
        (nb090AlphaDummy259 A) from (by
          unfold
            nb090AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0260
                    A)
                  0)))) (show (nb090AlphaDummy257 h) ≠ (nb090AlphaDummy260 h) from (by
          unfold
            nb090AlphaDummy260;
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
        ((nb090AlphaDummy281 A), (nb090AlphaDummy282 h)), ((nb090AlphaDummy279 A),
        (nb090AlphaDummy280 h)), ((nb090AlphaDummy248 A), (nb090AlphaDummy250 h)),
        ((nb090AlphaDummy247 A), (nb090AlphaDummy249 h)), ((nb090AlphaDummy277 A),
        (nb090AlphaDummy278 h)), ((nb090AlphaDummy251 A), (nb090AlphaDummy252 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A),
        (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy257 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy263
        A) ≠ (nb090AlphaDummy269 A) from (by
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
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy257 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy263
        A) ≠ (nb090AlphaDummy269 A) from (by
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
        ((nb090AlphaDummy281 A), (nb090AlphaDummy282 h)), ((nb090AlphaDummy279 A),
        (nb090AlphaDummy280 h)), ((nb090AlphaDummy248 A), (nb090AlphaDummy250 h)),
        ((nb090AlphaDummy247 A), (nb090AlphaDummy249 h)), ((nb090AlphaDummy277 A),
        (nb090AlphaDummy278 h)), ((nb090AlphaDummy251 A), (nb090AlphaDummy252 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A),
        (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A),
        v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy255 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy255 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy257
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy257 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy262
        A) ≠ (nb090AlphaDummy273 A) from (by
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
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy257 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy263 A) ≠ (nb090AlphaDummy275 A) from (by
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
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy255 A) ≠
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
                  (nb090_support_mem_0261 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb090AlphaDummy259 A), (nb090AlphaDummy260 h)),
        ((nb090AlphaDummy255 A), (nb090AlphaDummy257 h)), ((nb090AlphaDummy256 A),
        (nb090AlphaDummy258 h)), ((nb090AlphaDummy281 A), (nb090AlphaDummy282 h)),
        ((nb090AlphaDummy279 A), (nb090AlphaDummy280 h)), ((nb090AlphaDummy248 A),
        (nb090AlphaDummy250 h)), ((nb090AlphaDummy247 A), (nb090AlphaDummy249 h)),
        ((nb090AlphaDummy277 A), (nb090AlphaDummy278 h)), ((nb090AlphaDummy251 A),
        (nb090AlphaDummy252 h)), ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
        ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy255 A) ≠ (nb090AlphaDummy259 A) from (by
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
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb090AlphaDummy255 A) ≠ (nb090AlphaDummy259 A) from (by
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
        (TAlphaClass.reflOfClosed [((nb090AlphaDummy259 A), (nb090AlphaDummy260 h)),
        ((nb090AlphaDummy255 A), (nb090AlphaDummy257 h)), ((nb090AlphaDummy256 A),
        (nb090AlphaDummy258 h)), ((nb090AlphaDummy281 A), (nb090AlphaDummy282 h)),
        ((nb090AlphaDummy279 A), (nb090AlphaDummy280 h)), ((nb090AlphaDummy248 A),
        (nb090AlphaDummy250 h)), ((nb090AlphaDummy247 A), (nb090AlphaDummy249 h)),
        ((nb090AlphaDummy277 A), (nb090AlphaDummy278 h)), ((nb090AlphaDummy251 A),
        (nb090AlphaDummy252 h)), ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
        ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy248 A) ≠ (nb090AlphaDummy255 A) from
                                      (by
                                        unfold nb090AlphaDummy255;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0258 A)
                                                0)))) (show (nb090AlphaDummy250 h) ≠
                                        (nb090AlphaDummy257 h) from (by
                                        unfold nb090AlphaDummy257;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0259 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy248 A) ≠ (nb090AlphaDummy256 A)
                                        from (by
                                          unfold nb090AlphaDummy256;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0258 A) 1)))) (show
                                        (nb090AlphaDummy250 h) ≠ (nb090AlphaDummy258 h)
                                        from (by
                                          unfold nb090AlphaDummy258;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0259 h) 1))))
                                      (TAlphaVar.there (show (nb090AlphaDummy248 A) ≠
        (nb090AlphaDummy281 A) from (by
          unfold nb090AlphaDummy281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0288 A) 0)))) (show (nb090AlphaDummy250 h) ≠
        (nb090AlphaDummy282 h) from (by
          unfold nb090AlphaDummy282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0289 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy248 A) ≠ (nb090AlphaDummy279 A) from (by
          unfold nb090AlphaDummy279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0286 A) 0)))) (show (nb090AlphaDummy250 h) ≠
        (nb090AlphaDummy280 h) from (by
          unfold nb090AlphaDummy280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0287 h) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb090AlphaDummy248 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb090AlphaDummy250 h))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy255 A) ≠ (nb090AlphaDummy262 A) from (by
          unfold nb090AlphaDummy262;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0262
                    A)
                  1)))) (show (nb090AlphaDummy257 h) ≠ (nb090AlphaDummy265 h) from (by
          unfold nb090AlphaDummy265;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0263
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy255 A) ≠
        (nb090AlphaDummy261 A) from (by
          unfold nb090AlphaDummy261;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0262
                    A)
                  0)))) (show (nb090AlphaDummy257 h) ≠ (nb090AlphaDummy264 h) from (by
          unfold nb090AlphaDummy264;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0263
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy255 A) ≠
        (nb090AlphaDummy259 A) from (by
          unfold
            nb090AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0260
                    A)
                  0)))) (show (nb090AlphaDummy257 h) ≠ (nb090AlphaDummy260 h) from (by
          unfold
            nb090AlphaDummy260;
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
        ((nb090AlphaDummy281 A), (nb090AlphaDummy282 h)), ((nb090AlphaDummy279 A),
        (nb090AlphaDummy280 h)), ((nb090AlphaDummy248 A), (nb090AlphaDummy250 h)),
        ((nb090AlphaDummy247 A), (nb090AlphaDummy249 h)), ((nb090AlphaDummy277 A),
        (nb090AlphaDummy278 h)), ((nb090AlphaDummy251 A), (nb090AlphaDummy252 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A),
        (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy257 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy263
        A) ≠ (nb090AlphaDummy269 A) from (by
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
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy257 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy263
        A) ≠ (nb090AlphaDummy269 A) from (by
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
        ((nb090AlphaDummy281 A), (nb090AlphaDummy282 h)), ((nb090AlphaDummy279 A),
        (nb090AlphaDummy280 h)), ((nb090AlphaDummy248 A), (nb090AlphaDummy250 h)),
        ((nb090AlphaDummy247 A), (nb090AlphaDummy249 h)), ((nb090AlphaDummy277 A),
        (nb090AlphaDummy278 h)), ((nb090AlphaDummy251 A), (nb090AlphaDummy252 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A),
        (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A),
        v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy255 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy255 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy257
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy257 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy262
        A) ≠ (nb090AlphaDummy273 A) from (by
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
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy257 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy263 A) ≠ (nb090AlphaDummy275 A) from (by
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
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy255 A) ≠
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
                  (nb090_support_mem_0261 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb090AlphaDummy259 A), (nb090AlphaDummy260 h)),
        ((nb090AlphaDummy255 A), (nb090AlphaDummy257 h)), ((nb090AlphaDummy256 A),
        (nb090AlphaDummy258 h)), ((nb090AlphaDummy281 A), (nb090AlphaDummy282 h)),
        ((nb090AlphaDummy279 A), (nb090AlphaDummy280 h)), ((nb090AlphaDummy248 A),
        (nb090AlphaDummy250 h)), ((nb090AlphaDummy247 A), (nb090AlphaDummy249 h)),
        ((nb090AlphaDummy277 A), (nb090AlphaDummy278 h)), ((nb090AlphaDummy251 A),
        (nb090AlphaDummy252 h)), ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
        ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy255 A) ≠ (nb090AlphaDummy259 A) from (by
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
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb090AlphaDummy255 A) ≠ (nb090AlphaDummy259 A) from (by
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
        (TAlphaClass.reflOfClosed [((nb090AlphaDummy259 A), (nb090AlphaDummy260 h)),
        ((nb090AlphaDummy255 A), (nb090AlphaDummy257 h)), ((nb090AlphaDummy256 A),
        (nb090AlphaDummy258 h)), ((nb090AlphaDummy281 A), (nb090AlphaDummy282 h)),
        ((nb090AlphaDummy279 A), (nb090AlphaDummy280 h)), ((nb090AlphaDummy248 A),
        (nb090AlphaDummy250 h)), ((nb090AlphaDummy247 A), (nb090AlphaDummy249 h)),
        ((nb090AlphaDummy277 A), (nb090AlphaDummy278 h)), ((nb090AlphaDummy251 A),
        (nb090AlphaDummy252 h)), ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
        ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb090AlphaDummy279 A), (nb090AlphaDummy280 h)),
                    ((nb090AlphaDummy248 A), (nb090AlphaDummy250 h)),
                    ((nb090AlphaDummy247 A), (nb090AlphaDummy249 h)),
                    ((nb090AlphaDummy277 A), (nb090AlphaDummy278 h)),
                    ((nb090AlphaDummy251 A), (nb090AlphaDummy252 h)),
                    ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
                    ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
                    ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                    ((nb090AlphaDummy001 A), u),
                    ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                  (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part048`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0025`. -/
@[expose]
noncomputable def nb090SplitAlpha0025 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
        ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy141 A))
          (Class.cab (nb090AlphaDummy135 A)
            (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy129 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                (synCphi (Class.cv (nb090AlphaDummy136 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy141 A))
            (Class.cab (nb090AlphaDummy135 A)
              (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy129 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                  (synCphi (Class.cv (nb090AlphaDummy136 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy142 h))
          (Class.cab (nb090AlphaDummy137 h)
            (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy131 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                (synCphi (Class.cv (nb090AlphaDummy138 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy142 h))
            (Class.cab (nb090AlphaDummy137 h)
              (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy131 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                  (synCphi (Class.cv (nb090AlphaDummy138 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy136 A) from (by
                      unfold nb090AlphaDummy136;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0126 A) 1))))
                  (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy138 h) from (by
                      unfold nb090AlphaDummy138;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0128 h) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy135 A) from (by
                        unfold nb090AlphaDummy135;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0126 A) 0))))
                    (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy137 h) from (by
                        unfold nb090AlphaDummy137;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0128 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy141 A) from (by
                          unfold nb090AlphaDummy141;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0130 A) 0))))
                      (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy142 h) from (by
                          unfold nb090AlphaDummy142;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0131 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy139 A) from (by
                            unfold nb090AlphaDummy139;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0127 A) 0))))
                        (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy140 h) from (by
                            unfold nb090AlphaDummy140;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0129 h) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy000 A))).fv)
                            (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy129 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy130 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090AlphaDummy131 h))).fv ∪
                      ((Class.cv (nb090AlphaDummy132 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy143 A) from (by
                              unfold nb090AlphaDummy143;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                          (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy145 h) from (by
                              unfold nb090AlphaDummy145;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy144 A) from (by
                                unfold nb090AlphaDummy144;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                            (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy146 h) from (by
                                unfold nb090AlphaDummy146;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy136 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy138 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy150 A) from (by
          unfold nb090AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 1)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy153 h) from (by
          unfold nb090AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy149 A) from (by
          unfold nb090AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 0)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy152 h) from (by
          unfold nb090AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from (by
          unfold nb090AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A)
                  0)))) (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from (by
          unfold nb090AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy151 A), (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A),
        (nb090AlphaDummy153 h)), ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)),
        ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)), ((nb090AlphaDummy143 A),
        (nb090AlphaDummy145 h)), ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
        ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A),
        (nb090AlphaDummy137 h)), ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy244 A),
        (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy150
        A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy151 A), (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A),
        (nb090AlphaDummy153 h)), ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)),
        ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)), ((nb090AlphaDummy143 A),
        (nb090AlphaDummy145 h)), ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
        ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A),
        (nb090AlphaDummy137 h)), ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy244 A),
        (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy145
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy151
        A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy151
        A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from
                                      (by
                                        unfold nb090AlphaDummy147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090AlphaDummy145 h) ≠
                                        (nb090AlphaDummy148 h) from (by
                                        unfold nb090AlphaDummy148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                                    ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                                    ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                                    ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                                    ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                                    ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
                                    ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                                    ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                    ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                    ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                    ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
                                    ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from
                                    (by
                                      unfold nb090AlphaDummy147;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0134 A)
                                              0)))) (show
                                    (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from
                                    (by
                                      unfold nb090AlphaDummy148;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0135 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from
                                      (by
                                        unfold nb090AlphaDummy147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090AlphaDummy145 h) ≠
                                        (nb090AlphaDummy148 h) from (by
                                        unfold nb090AlphaDummy148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                                    ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                                    ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                                    ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                                    ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                                    ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
                                    ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                                    ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                    ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                    ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                    ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
                                    ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy136 A) from (by
                        unfold nb090AlphaDummy136;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0126 A) 1))))
                    (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy138 h) from (by
                        unfold nb090AlphaDummy138;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0128 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy135 A) from (by
                          unfold nb090AlphaDummy135;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0126 A) 0))))
                      (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy137 h) from (by
                          unfold nb090AlphaDummy137;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0128 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy141 A) from (by
                            unfold nb090AlphaDummy141;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0130 A) 0))))
                        (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy142 h) from (by
                            unfold nb090AlphaDummy142;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0131 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy139 A) from (by
                              unfold nb090AlphaDummy139;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0127 A) 0))))
                          (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy140 h) from (by
                              unfold nb090AlphaDummy140;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0129 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy000 A))).fv) (by decide))
                            (freshVar_injective (((Class.cv h)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy129 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy130 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy131 h))).fv ∪
                        ((Class.cv (nb090AlphaDummy132 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy143 A) from (by
                                unfold nb090AlphaDummy143;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                            (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy145 h) from (by
                                unfold nb090AlphaDummy145;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy144 A) from
                                (by
                                  unfold nb090AlphaDummy144;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                              (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy146 h) from
                                (by
                                  unfold nb090AlphaDummy146;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy136 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy138 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy150 A) from (by
          unfold nb090AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 1)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy153 h) from (by
          unfold nb090AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy149 A) from (by
          unfold nb090AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A)
                  0)))) (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy152 h) from (by
          unfold nb090AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy143 A) ≠
        (nb090AlphaDummy147 A) from (by
          unfold nb090AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A)
                  0)))) (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from (by
          unfold nb090AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy151 A), (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A),
        (nb090AlphaDummy153 h)), ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)),
        ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)), ((nb090AlphaDummy143 A),
        (nb090AlphaDummy145 h)), ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
        ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A),
        (nb090AlphaDummy137 h)), ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy244 A),
        (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy150
        A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy151 A), (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A),
        (nb090AlphaDummy153 h)), ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)),
        ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)), ((nb090AlphaDummy143 A),
        (nb090AlphaDummy145 h)), ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
        ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A),
        (nb090AlphaDummy137 h)), ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy244 A),
        (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy145
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy151
        A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy151
        A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A)
                                        from (by
                                          unfold nb090AlphaDummy147;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0134 A) 0)))) (show
                                        (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h)
                                        from (by
                                          unfold nb090AlphaDummy148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0135 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                                      ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                                      ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                                      ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                                      ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                                      ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
                                      ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                                      ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                      ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                      ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                      ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
                                      ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from
                                      (by
                                        unfold nb090AlphaDummy147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090AlphaDummy145 h) ≠
                                        (nb090AlphaDummy148 h) from (by
                                        unfold nb090AlphaDummy148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A)
                                        from (by
                                          unfold nb090AlphaDummy147;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0134 A) 0)))) (show
                                        (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h)
                                        from (by
                                          unfold nb090AlphaDummy148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0135 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                                      ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                                      ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                                      ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                                      ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                                      ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
                                      ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                                      ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                      ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                      ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                      ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
                                      ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part049`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0026`. -/
@[expose]
noncomputable def nb090SplitAlpha0026 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)),
        ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
        ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
        ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)),
        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
        ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.classMem (Class.cv (nb090AlphaDummy167 A))
        (synCcompl (synCphi (Class.cv (nb090AlphaDummy136 A)))))
      (Wff.classMem (Class.cv (nb090AlphaDummy168 h))
        (synCcompl (synCphi (Class.cv (nb090AlphaDummy138 h))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy143 A) from (by
                            unfold nb090AlphaDummy143;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                        (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy145 h) from (by
                            unfold nb090AlphaDummy145;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy144 A) from (by
                              unfold nb090AlphaDummy144;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                          (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy146 h) from (by
                              unfold nb090AlphaDummy146;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy169 A) from (by
                                unfold nb090AlphaDummy169;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0162 A) 0))))
                            (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy170 h) from (by
                                unfold nb090AlphaDummy170;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0163 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy167 A) from
                                (by
                                  unfold nb090AlphaDummy167;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0160 A) 0))))
                              (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy168 h) from
                                (by
                                  unfold nb090AlphaDummy168;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0161 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb090AlphaDummy136 A))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb090AlphaDummy138 h))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090AlphaDummy143 A) ≠
        (nb090AlphaDummy150 A) from (by
          unfold nb090AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 1)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy153 h) from (by
          unfold nb090AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy149 A) from (by
          unfold nb090AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 0)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy152 h) from (by
          unfold nb090AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from (by
          unfold nb090AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A) 0)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy148 h) from (by
          unfold nb090AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy151 A), (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A),
        (nb090AlphaDummy153 h)), ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)),
        ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)), ((nb090AlphaDummy143 A),
        (nb090AlphaDummy145 h)), ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
        ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)), ((nb090AlphaDummy167 A),
        (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
        ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)), ((nb090AlphaDummy165 A),
        (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A),
        (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A),
        (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy151 A), (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A),
        (nb090AlphaDummy153 h)), ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)),
        ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)), ((nb090AlphaDummy143 A),
        (nb090AlphaDummy145 h)), ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
        ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)), ((nb090AlphaDummy167 A),
        (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
        ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)), ((nb090AlphaDummy165 A),
        (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A),
        (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A),
        (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy145 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy150
        A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy151
        A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy151
        A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from
                                    (by
                                      unfold nb090AlphaDummy147;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0134 A)
                                              0)))) (show
                                    (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from
                                    (by
                                      unfold nb090AlphaDummy148;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0135 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                                  ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                                  ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                                  ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)),
                                  ((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)),
                                  ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                                  ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                                  ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)),
                                  ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                                  ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                  ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                  ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                  ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
                                  ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
                                  ((nb090AlphaDummy000 A), h),
                                  ((nb090AlphaDummy002 A), v),
                                  ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                    (nb090AlphaDummy004 v u A h))]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from (by
                                    unfold nb090AlphaDummy147;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0134 A)
                                            0)))) (show
                                  (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from (by
                                    unfold nb090AlphaDummy148;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0135 h)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from
                                    (by
                                      unfold nb090AlphaDummy147;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0134 A)
                                              0)))) (show
                                    (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from
                                    (by
                                      unfold nb090AlphaDummy148;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0135 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                                  ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                                  ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                                  ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)),
                                  ((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)),
                                  ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                                  ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                                  ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)),
                                  ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                                  ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                  ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                  ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                  ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
                                  ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
                                  ((nb090AlphaDummy000 A), h),
                                  ((nb090AlphaDummy002 A), v),
                                  ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                    (nb090AlphaDummy004 v u A h))]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy143 A) from (by
                            unfold nb090AlphaDummy143;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                        (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy145 h) from (by
                            unfold nb090AlphaDummy145;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy144 A) from (by
                              unfold nb090AlphaDummy144;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                          (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy146 h) from (by
                              unfold nb090AlphaDummy146;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy169 A) from (by
                                unfold nb090AlphaDummy169;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0162 A) 0))))
                            (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy170 h) from (by
                                unfold nb090AlphaDummy170;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0163 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy167 A) from
                                (by
                                  unfold nb090AlphaDummy167;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0160 A) 0))))
                              (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy168 h) from
                                (by
                                  unfold nb090AlphaDummy168;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0161 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb090AlphaDummy136 A))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb090AlphaDummy138 h))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090AlphaDummy143 A) ≠
        (nb090AlphaDummy150 A) from (by
          unfold nb090AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 1)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy153 h) from (by
          unfold nb090AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy149 A) from (by
          unfold nb090AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 0)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy152 h) from (by
          unfold nb090AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from (by
          unfold nb090AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A) 0)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy148 h) from (by
          unfold nb090AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy151 A), (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A),
        (nb090AlphaDummy153 h)), ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)),
        ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)), ((nb090AlphaDummy143 A),
        (nb090AlphaDummy145 h)), ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
        ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)), ((nb090AlphaDummy167 A),
        (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
        ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)), ((nb090AlphaDummy165 A),
        (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A),
        (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A),
        (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy151 A), (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A),
        (nb090AlphaDummy153 h)), ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)),
        ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)), ((nb090AlphaDummy143 A),
        (nb090AlphaDummy145 h)), ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
        ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)), ((nb090AlphaDummy167 A),
        (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
        ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)), ((nb090AlphaDummy165 A),
        (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A),
        (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A),
        (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy145 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy150
        A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy151
        A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy151
        A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from
                                    (by
                                      unfold nb090AlphaDummy147;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0134 A)
                                              0)))) (show
                                    (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from
                                    (by
                                      unfold nb090AlphaDummy148;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0135 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                                  ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                                  ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                                  ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)),
                                  ((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)),
                                  ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                                  ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                                  ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)),
                                  ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                                  ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                  ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                  ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                  ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
                                  ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
                                  ((nb090AlphaDummy000 A), h),
                                  ((nb090AlphaDummy002 A), v),
                                  ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                    (nb090AlphaDummy004 v u A h))]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from (by
                                    unfold nb090AlphaDummy147;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0134 A)
                                            0)))) (show
                                  (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from (by
                                    unfold nb090AlphaDummy148;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0135 h)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from
                                    (by
                                      unfold nb090AlphaDummy147;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0134 A)
                                              0)))) (show
                                    (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from
                                    (by
                                      unfold nb090AlphaDummy148;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0135 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                                  ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                                  ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                                  ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)),
                                  ((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)),
                                  ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                                  ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                                  ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)),
                                  ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                                  ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                  ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                  ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                  ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
                                  ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
                                  ((nb090AlphaDummy000 A), h),
                                  ((nb090AlphaDummy002 A), v),
                                  ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                    (nb090AlphaDummy004 v u A h))]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
