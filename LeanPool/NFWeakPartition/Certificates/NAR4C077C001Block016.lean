/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C077C001Block015

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C077C001Part045`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb077_split_alpha_0031`. -/
@[expose]
noncomputable def nb077SplitAlpha0031 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077AlphaDummy293 F I), (nb077AlphaDummy294 x)),
        ((nb077AlphaDummy291 F I), (nb077AlphaDummy292 x)),
        ((nb077AlphaDummy260 F I), (nb077AlphaDummy262 x)),
        ((nb077AlphaDummy259 F I), (nb077AlphaDummy261 x)),
        ((nb077AlphaDummy289 F I), (nb077AlphaDummy290 x)),
        ((nb077AlphaDummy263 F I), (nb077AlphaDummy264 x)),
        ((nb077AlphaDummy255 F I), (nb077AlphaDummy256 x)),
        ((nb077AlphaDummy000 F I), x),
        ((nb077AlphaDummy257 F I), (nb077AlphaDummy258 x)),
        ((nb077AlphaDummy141 F I), (nb077AlphaDummy144 x)),
        ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
        ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
        ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
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
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy293 F I))
          (synCphi (Class.cv (nb077AlphaDummy260 F I)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy293 F I))
            (synCphi (Class.cv (nb077AlphaDummy260 F I))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy294 x))
          (synCphi (Class.cv (nb077AlphaDummy262 x)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy294 x))
            (synCphi (Class.cv (nb077AlphaDummy262 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077AlphaDummy260 F I) ≠ (nb077AlphaDummy267 F I) from (by
                      unfold nb077AlphaDummy267;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0258 F I) 0))))
                  (show (nb077AlphaDummy262 x) ≠ (nb077AlphaDummy269 x) from (by
                      unfold nb077AlphaDummy269;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0259 x) 0))))
                  (TAlphaVar.there
                    (show (nb077AlphaDummy260 F I) ≠ (nb077AlphaDummy268 F I) from (by
                        unfold nb077AlphaDummy268;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0258 F I) 1))))
                    (show (nb077AlphaDummy262 x) ≠ (nb077AlphaDummy270 x) from (by
                        unfold nb077AlphaDummy270;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0259 x) 1)))) (TAlphaVar.there
                      (show (nb077AlphaDummy260 F I) ≠ (nb077AlphaDummy293 F I) from (by
                          unfold nb077AlphaDummy293;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0288 F I) 0))))
                      (show (nb077AlphaDummy262 x) ≠ (nb077AlphaDummy294 x) from (by
                          unfold nb077AlphaDummy294;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0289 x) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy260 F I) ≠ (nb077AlphaDummy291 F I) from (by
                            unfold nb077AlphaDummy291;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0286 F I) 0))))
                        (show (nb077AlphaDummy262 x) ≠ (nb077AlphaDummy292 x) from (by
                            unfold nb077AlphaDummy292;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0287 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb077AlphaDummy260 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077AlphaDummy262 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy267 F I) ≠ (nb077AlphaDummy274 F I)
                                      from (by
                                        unfold nb077AlphaDummy274;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0262 F I) 1)))) (show
                                      (nb077AlphaDummy269 x) ≠ (nb077AlphaDummy277 x) from
                                      (by
                                        unfold nb077AlphaDummy277;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0263 x)
                                                1)))) (TAlphaVar.there (show
                                        (nb077AlphaDummy267 F I) ≠
        (nb077AlphaDummy273 F I) from (by
                                          unfold nb077AlphaDummy273;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0262 F I) 0)))) (show
                                        (nb077AlphaDummy269 x) ≠ (nb077AlphaDummy276 x)
                                        from (by
                                          unfold nb077AlphaDummy276;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0263 x) 0))))
                                      (TAlphaVar.there (show (nb077AlphaDummy267 F I) ≠
        (nb077AlphaDummy271 F I) from (by
          unfold nb077AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0260 F I) 0)))) (show (nb077AlphaDummy269 x) ≠
        (nb077AlphaDummy272 x) from (by
          unfold nb077AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0261 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb077AlphaDummy275 F I),
        (nb077AlphaDummy278 x)), ((nb077AlphaDummy274 F I), (nb077AlphaDummy277 x)),
                                        ((nb077AlphaDummy273 F I),
        (nb077AlphaDummy276 x)), ((nb077AlphaDummy271 F I), (nb077AlphaDummy272 x)),
                                        ((nb077AlphaDummy267 F I),
        (nb077AlphaDummy269 x)), ((nb077AlphaDummy268 F I), (nb077AlphaDummy270 x)),
                                        ((nb077AlphaDummy293 F I),
        (nb077AlphaDummy294 x)), ((nb077AlphaDummy291 F I), (nb077AlphaDummy292 x)),
                                        ((nb077AlphaDummy260 F I),
        (nb077AlphaDummy262 x)), ((nb077AlphaDummy259 F I), (nb077AlphaDummy261 x)),
                                        ((nb077AlphaDummy289 F I),
        (nb077AlphaDummy290 x)), ((nb077AlphaDummy263 F I), (nb077AlphaDummy264 x)),
                                        ((nb077AlphaDummy255 F I),
        (nb077AlphaDummy256 x)), ((nb077AlphaDummy000 F I), x),
                                        ((nb077AlphaDummy257 F I),
        (nb077AlphaDummy258 x)), ((nb077AlphaDummy141 F I), (nb077AlphaDummy144 x)),
                                        ((nb077AlphaDummy140 F I),
        (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
                                        ((nb077AlphaDummy145 F I),
        (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                                        ((nb077AlphaDummy060 F I),
        (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                                        ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                                        ((nb077AlphaDummy055 F I),
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
        (nb077AlphaDummy274 F I) ≠ (nb077AlphaDummy281 F I) from (by
          unfold
            nb077AlphaDummy281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0266
                    F I)
                  0)))) (show (nb077AlphaDummy277 x) ≠ (nb077AlphaDummy282 x) from (by
          unfold
            nb077AlphaDummy282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0267
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy274 F I) ≠
        (nb077AlphaDummy279 F I) from (by
          unfold
            nb077AlphaDummy279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0264
                    F I)
                  0)))) (show (nb077AlphaDummy277 x) ≠ (nb077AlphaDummy280 x) from (by
          unfold
            nb077AlphaDummy280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0265
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy267
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy275 F I) ≠
        (nb077AlphaDummy281 F I) from (by
          unfold
            nb077AlphaDummy281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0270
                    F I)
                  0)))) (show (nb077AlphaDummy278 x) ≠ (nb077AlphaDummy282 x) from (by
          unfold
            nb077AlphaDummy282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0271
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy275 F I) ≠
        (nb077AlphaDummy279 F I) from (by
          unfold
            nb077AlphaDummy279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0268
                    F I)
                  0)))) (show (nb077AlphaDummy278 x) ≠ (nb077AlphaDummy280 x) from (by
          unfold
            nb077AlphaDummy280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0269
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy274 F I) ≠ (nb077AlphaDummy281 F I) from
        (by
          unfold
            nb077AlphaDummy281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0266
                    F I)
                  0)))) (show (nb077AlphaDummy277 x) ≠ (nb077AlphaDummy282 x) from (by
          unfold
            nb077AlphaDummy282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0267
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy274 F I) ≠
        (nb077AlphaDummy279 F I) from (by
          unfold
            nb077AlphaDummy279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0264
                    F I)
                  0)))) (show (nb077AlphaDummy277 x) ≠ (nb077AlphaDummy280 x) from (by
          unfold
            nb077AlphaDummy280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0265
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy267
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy275 F I) ≠
        (nb077AlphaDummy281 F I) from (by
          unfold
            nb077AlphaDummy281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0270
                    F I)
                  0)))) (show (nb077AlphaDummy278 x) ≠ (nb077AlphaDummy282 x) from (by
          unfold
            nb077AlphaDummy282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0271
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy275 F I) ≠
        (nb077AlphaDummy279 F I) from (by
          unfold
            nb077AlphaDummy279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0268
                    F I)
                  0)))) (show (nb077AlphaDummy278 x) ≠ (nb077AlphaDummy280 x) from (by
          unfold
            nb077AlphaDummy280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0269
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb077AlphaDummy275 F I),
        (nb077AlphaDummy278 x)), ((nb077AlphaDummy274 F I), (nb077AlphaDummy277 x)),
        ((nb077AlphaDummy273 F I), (nb077AlphaDummy276 x)), ((nb077AlphaDummy271 F I),
        (nb077AlphaDummy272 x)), ((nb077AlphaDummy267 F I), (nb077AlphaDummy269 x)),
        ((nb077AlphaDummy268 F I), (nb077AlphaDummy270 x)), ((nb077AlphaDummy293 F I),
        (nb077AlphaDummy294 x)), ((nb077AlphaDummy291 F I), (nb077AlphaDummy292 x)),
        ((nb077AlphaDummy260 F I), (nb077AlphaDummy262 x)), ((nb077AlphaDummy259 F I),
        (nb077AlphaDummy261 x)), ((nb077AlphaDummy289 F I), (nb077AlphaDummy290 x)),
        ((nb077AlphaDummy263 F I), (nb077AlphaDummy264 x)), ((nb077AlphaDummy255 F I),
        (nb077AlphaDummy256 x)), ((nb077AlphaDummy000 F I), x),
        ((nb077AlphaDummy257 F I), (nb077AlphaDummy258 x)), ((nb077AlphaDummy141 F I),
        (nb077AlphaDummy144 x)), ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
        ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I),
        (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
        (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077AlphaDummy267 F I))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy267 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy274 F I) ≠ (nb077AlphaDummy285 F I) from (by
          unfold
            nb077AlphaDummy285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0274
                    F I)
                  0)))) (show (nb077AlphaDummy277 x) ≠ (nb077AlphaDummy286 x) from (by
          unfold
            nb077AlphaDummy286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0275
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy274 F I) ≠
        (nb077AlphaDummy283 F I) from (by
          unfold
            nb077AlphaDummy283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0272
                    F I)
                  0)))) (show (nb077AlphaDummy277 x) ≠ (nb077AlphaDummy284 x) from (by
          unfold
            nb077AlphaDummy284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0273
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy267
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy274 F I) ≠
        (nb077AlphaDummy285 F I) from (by
          unfold
            nb077AlphaDummy285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0274
                    F I)
                  0)))) (show (nb077AlphaDummy277 x) ≠ (nb077AlphaDummy286 x) from (by
          unfold
            nb077AlphaDummy286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0275
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy274 F I) ≠
        (nb077AlphaDummy283 F I) from (by
          unfold
            nb077AlphaDummy283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0272
                    F I)
                  0)))) (show (nb077AlphaDummy277 x) ≠ (nb077AlphaDummy284 x) from (by
          unfold
            nb077AlphaDummy284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0273
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy267
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy275 F I) ≠ (nb077AlphaDummy287 F I) from (by
          unfold
            nb077AlphaDummy287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0278
                    F I)
                  0)))) (show (nb077AlphaDummy278 x) ≠ (nb077AlphaDummy288 x) from (by
          unfold
            nb077AlphaDummy288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0279
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy275 F I) ≠
        (nb077AlphaDummy283 F I) from (by
          unfold
            nb077AlphaDummy283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0276
                    F I)
                  0)))) (show (nb077AlphaDummy278 x) ≠ (nb077AlphaDummy284 x) from (by
          unfold
            nb077AlphaDummy284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0277
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy275 F I) ≠ (nb077AlphaDummy287 F I) from (by
          unfold
            nb077AlphaDummy287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0278
                    F I)
                  0)))) (show (nb077AlphaDummy278 x) ≠ (nb077AlphaDummy288 x) from (by
          unfold
            nb077AlphaDummy288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0279
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy275 F I) ≠
        (nb077AlphaDummy283 F I) from (by
          unfold
            nb077AlphaDummy283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0276
                    F I)
                  0)))) (show (nb077AlphaDummy278 x) ≠ (nb077AlphaDummy284 x) from (by
          unfold
            nb077AlphaDummy284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0277
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy267 F I) ≠ (nb077AlphaDummy271 F I) from (by
                                unfold nb077AlphaDummy271;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0260 F I) 0))))
                            (show (nb077AlphaDummy269 x) ≠ (nb077AlphaDummy272 x) from (by
                                unfold nb077AlphaDummy272;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0261 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb077AlphaDummy271 F I), (nb077AlphaDummy272 x)),
                            ((nb077AlphaDummy267 F I), (nb077AlphaDummy269 x)),
                            ((nb077AlphaDummy268 F I), (nb077AlphaDummy270 x)),
                            ((nb077AlphaDummy293 F I), (nb077AlphaDummy294 x)),
                            ((nb077AlphaDummy291 F I), (nb077AlphaDummy292 x)),
                            ((nb077AlphaDummy260 F I), (nb077AlphaDummy262 x)),
                            ((nb077AlphaDummy259 F I), (nb077AlphaDummy261 x)),
                            ((nb077AlphaDummy289 F I), (nb077AlphaDummy290 x)),
                            ((nb077AlphaDummy263 F I), (nb077AlphaDummy264 x)),
                            ((nb077AlphaDummy255 F I), (nb077AlphaDummy256 x)),
                            ((nb077AlphaDummy000 F I), x),
                            ((nb077AlphaDummy257 F I), (nb077AlphaDummy258 x)),
                            ((nb077AlphaDummy141 F I), (nb077AlphaDummy144 x)),
                            ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
                            ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
                            ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
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
                          (show (nb077AlphaDummy267 F I) ≠ (nb077AlphaDummy271 F I) from
                            (by
                              unfold nb077AlphaDummy271;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0260 F I) 0))))
                          (show (nb077AlphaDummy269 x) ≠ (nb077AlphaDummy272 x) from (by
                              unfold nb077AlphaDummy272;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0261 x) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy267 F I) ≠ (nb077AlphaDummy271 F I) from (by
                                unfold nb077AlphaDummy271;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0260 F I) 0))))
                            (show (nb077AlphaDummy269 x) ≠ (nb077AlphaDummy272 x) from (by
                                unfold nb077AlphaDummy272;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0261 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb077AlphaDummy271 F I), (nb077AlphaDummy272 x)),
                            ((nb077AlphaDummy267 F I), (nb077AlphaDummy269 x)),
                            ((nb077AlphaDummy268 F I), (nb077AlphaDummy270 x)),
                            ((nb077AlphaDummy293 F I), (nb077AlphaDummy294 x)),
                            ((nb077AlphaDummy291 F I), (nb077AlphaDummy292 x)),
                            ((nb077AlphaDummy260 F I), (nb077AlphaDummy262 x)),
                            ((nb077AlphaDummy259 F I), (nb077AlphaDummy261 x)),
                            ((nb077AlphaDummy289 F I), (nb077AlphaDummy290 x)),
                            ((nb077AlphaDummy263 F I), (nb077AlphaDummy264 x)),
                            ((nb077AlphaDummy255 F I), (nb077AlphaDummy256 x)),
                            ((nb077AlphaDummy000 F I), x),
                            ((nb077AlphaDummy257 F I), (nb077AlphaDummy258 x)),
                            ((nb077AlphaDummy141 F I), (nb077AlphaDummy144 x)),
                            ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
                            ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
                            ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
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
                    (show (nb077AlphaDummy260 F I) ≠ (nb077AlphaDummy267 F I) from (by
                        unfold nb077AlphaDummy267;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0258 F I) 0))))
                    (show (nb077AlphaDummy262 x) ≠ (nb077AlphaDummy269 x) from (by
                        unfold nb077AlphaDummy269;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0259 x) 0)))) (TAlphaVar.there
                      (show (nb077AlphaDummy260 F I) ≠ (nb077AlphaDummy268 F I) from (by
                          unfold nb077AlphaDummy268;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0258 F I) 1))))
                      (show (nb077AlphaDummy262 x) ≠ (nb077AlphaDummy270 x) from (by
                          unfold nb077AlphaDummy270;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0259 x) 1))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy260 F I) ≠ (nb077AlphaDummy293 F I) from (by
                            unfold nb077AlphaDummy293;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0288 F I) 0))))
                        (show (nb077AlphaDummy262 x) ≠ (nb077AlphaDummy294 x) from (by
                            unfold nb077AlphaDummy294;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0289 x) 0))))
                        (TAlphaVar.there
                          (show (nb077AlphaDummy260 F I) ≠ (nb077AlphaDummy291 F I) from
                            (by
                              unfold nb077AlphaDummy291;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0286 F I) 0))))
                          (show (nb077AlphaDummy262 x) ≠ (nb077AlphaDummy292 x) from (by
                              unfold nb077AlphaDummy292;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0287 x) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb077AlphaDummy260 F I))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb077AlphaDummy262 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb077AlphaDummy267 F I) ≠
        (nb077AlphaDummy274 F I) from (by
                                          unfold nb077AlphaDummy274;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0262 F I) 1)))) (show
                                        (nb077AlphaDummy269 x) ≠ (nb077AlphaDummy277 x)
                                        from (by
                                          unfold nb077AlphaDummy277;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0263 x) 1))))
                                      (TAlphaVar.there (show (nb077AlphaDummy267 F I) ≠
        (nb077AlphaDummy273 F I) from (by
          unfold nb077AlphaDummy273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0262 F I) 0)))) (show (nb077AlphaDummy269 x) ≠
        (nb077AlphaDummy276 x) from (by
          unfold nb077AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0263 x) 0)))) (TAlphaVar.there (show
        (nb077AlphaDummy267 F I) ≠ (nb077AlphaDummy271 F I) from (by
          unfold nb077AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0260 F I) 0)))) (show (nb077AlphaDummy269 x) ≠
        (nb077AlphaDummy272 x) from (by
          unfold nb077AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0261 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb077AlphaDummy275 F I),
        (nb077AlphaDummy278 x)), ((nb077AlphaDummy274 F I), (nb077AlphaDummy277 x)),
        ((nb077AlphaDummy273 F I), (nb077AlphaDummy276 x)), ((nb077AlphaDummy271 F I),
        (nb077AlphaDummy272 x)), ((nb077AlphaDummy267 F I), (nb077AlphaDummy269 x)),
        ((nb077AlphaDummy268 F I), (nb077AlphaDummy270 x)), ((nb077AlphaDummy293 F I),
        (nb077AlphaDummy294 x)), ((nb077AlphaDummy291 F I), (nb077AlphaDummy292 x)),
        ((nb077AlphaDummy260 F I), (nb077AlphaDummy262 x)), ((nb077AlphaDummy259 F I),
        (nb077AlphaDummy261 x)), ((nb077AlphaDummy289 F I), (nb077AlphaDummy290 x)),
        ((nb077AlphaDummy263 F I), (nb077AlphaDummy264 x)), ((nb077AlphaDummy255 F I),
        (nb077AlphaDummy256 x)), ((nb077AlphaDummy000 F I), x),
        ((nb077AlphaDummy257 F I), (nb077AlphaDummy258 x)), ((nb077AlphaDummy141 F I),
        (nb077AlphaDummy144 x)), ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
        ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I),
        (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
        (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy274 F
        I) ≠ (nb077AlphaDummy281 F I) from (by
          unfold
            nb077AlphaDummy281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0266
                    F I)
                  0)))) (show (nb077AlphaDummy277 x) ≠ (nb077AlphaDummy282 x) from (by
          unfold
            nb077AlphaDummy282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0267
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy274 F I) ≠
        (nb077AlphaDummy279 F I) from (by
          unfold
            nb077AlphaDummy279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0264
                    F I)
                  0)))) (show (nb077AlphaDummy277 x) ≠ (nb077AlphaDummy280 x) from (by
          unfold
            nb077AlphaDummy280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0265
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy267
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy275 F I) ≠ (nb077AlphaDummy281 F I) from
        (by
          unfold
            nb077AlphaDummy281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0270
                    F I)
                  0)))) (show (nb077AlphaDummy278 x) ≠ (nb077AlphaDummy282 x) from (by
          unfold
            nb077AlphaDummy282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0271
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy275 F I) ≠
        (nb077AlphaDummy279 F I) from (by
          unfold
            nb077AlphaDummy279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0268
                    F I)
                  0)))) (show (nb077AlphaDummy278 x) ≠ (nb077AlphaDummy280 x) from (by
          unfold
            nb077AlphaDummy280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0269
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy274 F I) ≠ (nb077AlphaDummy281 F I) from
        (by
          unfold
            nb077AlphaDummy281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0266
                    F I)
                  0)))) (show (nb077AlphaDummy277 x) ≠ (nb077AlphaDummy282 x) from (by
          unfold
            nb077AlphaDummy282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0267
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy274 F I) ≠
        (nb077AlphaDummy279 F I) from (by
          unfold
            nb077AlphaDummy279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0264
                    F I)
                  0)))) (show (nb077AlphaDummy277 x) ≠ (nb077AlphaDummy280 x) from (by
          unfold
            nb077AlphaDummy280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0265
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy267
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy275 F I) ≠ (nb077AlphaDummy281 F I) from
        (by
          unfold
            nb077AlphaDummy281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0270
                    F I)
                  0)))) (show (nb077AlphaDummy278 x) ≠ (nb077AlphaDummy282 x) from (by
          unfold
            nb077AlphaDummy282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0271
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy275 F I) ≠
        (nb077AlphaDummy279 F I) from (by
          unfold
            nb077AlphaDummy279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0268
                    F I)
                  0)))) (show (nb077AlphaDummy278 x) ≠ (nb077AlphaDummy280 x) from (by
          unfold
            nb077AlphaDummy280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0269
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy275 F I), (nb077AlphaDummy278 x)), ((nb077AlphaDummy274 F I),
        (nb077AlphaDummy277 x)), ((nb077AlphaDummy273 F I), (nb077AlphaDummy276 x)),
        ((nb077AlphaDummy271 F I), (nb077AlphaDummy272 x)), ((nb077AlphaDummy267 F I),
        (nb077AlphaDummy269 x)), ((nb077AlphaDummy268 F I), (nb077AlphaDummy270 x)),
        ((nb077AlphaDummy293 F I), (nb077AlphaDummy294 x)), ((nb077AlphaDummy291 F I),
        (nb077AlphaDummy292 x)), ((nb077AlphaDummy260 F I), (nb077AlphaDummy262 x)),
        ((nb077AlphaDummy259 F I), (nb077AlphaDummy261 x)), ((nb077AlphaDummy289 F I),
        (nb077AlphaDummy290 x)), ((nb077AlphaDummy263 F I), (nb077AlphaDummy264 x)),
        ((nb077AlphaDummy255 F I), (nb077AlphaDummy256 x)),
        ((nb077AlphaDummy000 F I), x), ((nb077AlphaDummy257 F I),
        (nb077AlphaDummy258 x)), ((nb077AlphaDummy141 F I), (nb077AlphaDummy144 x)),
        ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I),
        (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
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
        (((Class.cv (nb077AlphaDummy267 F I))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy267 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy274 F
        I) ≠ (nb077AlphaDummy285 F I) from (by
          unfold
            nb077AlphaDummy285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0274
                    F I)
                  0)))) (show (nb077AlphaDummy277 x) ≠ (nb077AlphaDummy286 x) from (by
          unfold
            nb077AlphaDummy286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0275
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy274 F I) ≠
        (nb077AlphaDummy283 F I) from (by
          unfold
            nb077AlphaDummy283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0272
                    F I)
                  0)))) (show (nb077AlphaDummy277 x) ≠ (nb077AlphaDummy284 x) from (by
          unfold
            nb077AlphaDummy284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0273
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy267
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy274 F I) ≠ (nb077AlphaDummy285 F I) from
        (by
          unfold
            nb077AlphaDummy285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0274
                    F I)
                  0)))) (show (nb077AlphaDummy277 x) ≠ (nb077AlphaDummy286 x) from (by
          unfold
            nb077AlphaDummy286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0275
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy274 F I) ≠
        (nb077AlphaDummy283 F I) from (by
          unfold
            nb077AlphaDummy283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0272
                    F I)
                  0)))) (show (nb077AlphaDummy277 x) ≠ (nb077AlphaDummy284 x) from (by
          unfold
            nb077AlphaDummy284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0273
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy267
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy275 F
        I) ≠ (nb077AlphaDummy287 F I) from (by
          unfold
            nb077AlphaDummy287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0278
                    F I)
                  0)))) (show (nb077AlphaDummy278 x) ≠ (nb077AlphaDummy288 x) from (by
          unfold
            nb077AlphaDummy288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0279
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy275 F I) ≠
        (nb077AlphaDummy283 F I) from (by
          unfold
            nb077AlphaDummy283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0276
                    F I)
                  0)))) (show (nb077AlphaDummy278 x) ≠ (nb077AlphaDummy284 x) from (by
          unfold
            nb077AlphaDummy284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0277
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy275 F
        I) ≠ (nb077AlphaDummy287 F I) from (by
          unfold
            nb077AlphaDummy287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0278
                    F I)
                  0)))) (show (nb077AlphaDummy278 x) ≠ (nb077AlphaDummy288 x) from (by
          unfold
            nb077AlphaDummy288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0279
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy275 F I) ≠
        (nb077AlphaDummy283 F I) from (by
          unfold
            nb077AlphaDummy283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0276
                    F I)
                  0)))) (show (nb077AlphaDummy278 x) ≠ (nb077AlphaDummy284 x) from (by
          unfold
            nb077AlphaDummy284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0277
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077AlphaDummy267 F I) ≠ (nb077AlphaDummy271 F I) from
                                (by
                                  unfold nb077AlphaDummy271;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0260 F I)
                                          0))))
                              (show (nb077AlphaDummy269 x) ≠ (nb077AlphaDummy272 x) from
                                (by
                                  unfold nb077AlphaDummy272;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0261 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb077AlphaDummy271 F I), (nb077AlphaDummy272 x)),
                              ((nb077AlphaDummy267 F I), (nb077AlphaDummy269 x)),
                              ((nb077AlphaDummy268 F I), (nb077AlphaDummy270 x)),
                              ((nb077AlphaDummy293 F I), (nb077AlphaDummy294 x)),
                              ((nb077AlphaDummy291 F I), (nb077AlphaDummy292 x)),
                              ((nb077AlphaDummy260 F I), (nb077AlphaDummy262 x)),
                              ((nb077AlphaDummy259 F I), (nb077AlphaDummy261 x)),
                              ((nb077AlphaDummy289 F I), (nb077AlphaDummy290 x)),
                              ((nb077AlphaDummy263 F I), (nb077AlphaDummy264 x)),
                              ((nb077AlphaDummy255 F I), (nb077AlphaDummy256 x)),
                              ((nb077AlphaDummy000 F I), x),
                              ((nb077AlphaDummy257 F I), (nb077AlphaDummy258 x)),
                              ((nb077AlphaDummy141 F I), (nb077AlphaDummy144 x)),
                              ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
                              ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
                              ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
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
                              (nb077AlphaDummy267 F I) ≠ (nb077AlphaDummy271 F I) from (by
                                unfold nb077AlphaDummy271;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0260 F I) 0))))
                            (show (nb077AlphaDummy269 x) ≠ (nb077AlphaDummy272 x) from (by
                                unfold nb077AlphaDummy272;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0261 x) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077AlphaDummy267 F I) ≠ (nb077AlphaDummy271 F I) from
                                (by
                                  unfold nb077AlphaDummy271;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0260 F I)
                                          0))))
                              (show (nb077AlphaDummy269 x) ≠ (nb077AlphaDummy272 x) from
                                (by
                                  unfold nb077AlphaDummy272;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0261 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb077AlphaDummy271 F I), (nb077AlphaDummy272 x)),
                              ((nb077AlphaDummy267 F I), (nb077AlphaDummy269 x)),
                              ((nb077AlphaDummy268 F I), (nb077AlphaDummy270 x)),
                              ((nb077AlphaDummy293 F I), (nb077AlphaDummy294 x)),
                              ((nb077AlphaDummy291 F I), (nb077AlphaDummy292 x)),
                              ((nb077AlphaDummy260 F I), (nb077AlphaDummy262 x)),
                              ((nb077AlphaDummy259 F I), (nb077AlphaDummy261 x)),
                              ((nb077AlphaDummy289 F I), (nb077AlphaDummy290 x)),
                              ((nb077AlphaDummy263 F I), (nb077AlphaDummy264 x)),
                              ((nb077AlphaDummy255 F I), (nb077AlphaDummy256 x)),
                              ((nb077AlphaDummy000 F I), x),
                              ((nb077AlphaDummy257 F I), (nb077AlphaDummy258 x)),
                              ((nb077AlphaDummy141 F I), (nb077AlphaDummy144 x)),
                              ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
                              ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
                              ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
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


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part046`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb077_split_alpha_0032`. -/
@[expose]
noncomputable def nb077SplitAlpha0032 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077AlphaDummy141 F I), (nb077AlphaDummy144 x)),
        ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
        ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
        ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
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
      (Wff.imp (synWbr (Class.cv (nb077AlphaDummy139 F I)) (synC1st)
          (Class.cv (nb077AlphaDummy141 F I))) (Wff.neg
          (synWbr (Class.cv (nb077AlphaDummy141 F I))
            (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))
            (Class.cv (nb077AlphaDummy140 F I)))))
      (Wff.imp (synWbr (Class.cv (nb077AlphaDummy142 x)) (synC1st)
          (Class.cv (nb077AlphaDummy144 x))) (Wff.neg
          (synWbr (Class.cv (nb077AlphaDummy144 x))
            (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))
            (Class.cv (nb077AlphaDummy143 x))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb077SplitAlpha0026 x F I)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb077AlphaDummy141 F I) ≠ (nb077AlphaDummy184 F I)
                                    from (by
                                      unfold nb077AlphaDummy184;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0198 F I)
                                              1)))) (show
                                    (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy186 x) from
                                    (by
                                      unfold nb077AlphaDummy186;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0200 x)
                                              1)))) (TAlphaVar.there (show
                                      (nb077AlphaDummy141 F I) ≠ (nb077AlphaDummy183 F I)
                                      from (by
                                        unfold nb077AlphaDummy183;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0198 F I) 0)))) (show
                                      (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy185 x) from
                                      (by
                                        unfold nb077AlphaDummy185;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0200 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb077AlphaDummy141 F I) ≠
        (nb077AlphaDummy213 F I) from (by
                                          unfold nb077AlphaDummy213;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0202 F I) 0)))) (show
                                        (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy214 x)
                                        from (by
                                          unfold nb077AlphaDummy214;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0203 x) 0))))
                                      (TAlphaVar.there (show (nb077AlphaDummy141 F I) ≠
        (nb077AlphaDummy187 F I) from (by
          unfold nb077AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0199 F I) 0)))) (show (nb077AlphaDummy144 x) ≠
        (nb077AlphaDummy188 x) from (by
          unfold nb077AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0201 x) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
                                      ((Class.cv (nb077AlphaDummy141 F I))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb077AlphaDummy142 x))).fv ∪
                                      ((Class.cv (nb077AlphaDummy144 x))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb077SplitAlpha0027 x F I))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb077AlphaDummy215 F I),
        (nb077AlphaDummy216 x)), ((nb077AlphaDummy184 F I), (nb077AlphaDummy186 x)),
        ((nb077AlphaDummy183 F I), (nb077AlphaDummy185 x)), ((nb077AlphaDummy213 F I),
        (nb077AlphaDummy214 x)), ((nb077AlphaDummy187 F I), (nb077AlphaDummy188 x)),
        ((nb077AlphaDummy141 F I), (nb077AlphaDummy144 x)), ((nb077AlphaDummy140 F I),
        (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
        ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                                        (synCcompl (synCsn (synC0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c])))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb077AlphaDummy141 F I) ≠ (nb077AlphaDummy184 F I)
                                    from (by
                                      unfold nb077AlphaDummy184;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0198 F I)
                                              1)))) (show
                                    (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy186 x) from
                                    (by
                                      unfold nb077AlphaDummy186;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0200 x)
                                              1)))) (TAlphaVar.there (show
                                      (nb077AlphaDummy141 F I) ≠ (nb077AlphaDummy183 F I)
                                      from (by
                                        unfold nb077AlphaDummy183;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0198 F I) 0)))) (show
                                      (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy185 x) from
                                      (by
                                        unfold nb077AlphaDummy185;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0200 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb077AlphaDummy141 F I) ≠
        (nb077AlphaDummy213 F I) from (by
                                          unfold nb077AlphaDummy213;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0202 F I) 0)))) (show
                                        (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy214 x)
                                        from (by
                                          unfold nb077AlphaDummy214;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0203 x) 0))))
                                      (TAlphaVar.there (show (nb077AlphaDummy141 F I) ≠
        (nb077AlphaDummy187 F I) from (by
          unfold nb077AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0199 F I) 0)))) (show (nb077AlphaDummy144 x) ≠
        (nb077AlphaDummy188 x) from (by
          unfold nb077AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0201 x) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
                                      ((Class.cv (nb077AlphaDummy141 F I))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb077AlphaDummy142 x))).fv ∪
                                      ((Class.cv (nb077AlphaDummy144 x))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb077SplitAlpha0027 x F I))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb077AlphaDummy215 F I),
        (nb077AlphaDummy216 x)), ((nb077AlphaDummy184 F I), (nb077AlphaDummy186 x)),
        ((nb077AlphaDummy183 F I), (nb077AlphaDummy185 x)), ((nb077AlphaDummy213 F I),
        (nb077AlphaDummy214 x)), ((nb077AlphaDummy187 F I), (nb077AlphaDummy188 x)),
        ((nb077AlphaDummy141 F I), (nb077AlphaDummy144 x)), ((nb077AlphaDummy140 F I),
        (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
        ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                                        (synCcompl (synCsn (synC0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c]))))))))))))))))))
      (TAlphaClass.reflOfReflOn [((nb077AlphaDummy141 F I), (nb077AlphaDummy144 x)),
          ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
          ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
          ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
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
        (synC1st) (nb077WppRefl0099 x F I))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb077SplitAlpha0028 x F I)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy140 F I) ≠ (nb077AlphaDummy220 F I)
                                      from (by
                                        unfold nb077AlphaDummy220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0236 F I) 1)))) (show
                                      (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy222 x) from
                                      (by
                                        unfold nb077AlphaDummy222;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0238 x)
                                                1)))) (TAlphaVar.there (show
                                        (nb077AlphaDummy140 F I) ≠
        (nb077AlphaDummy219 F I) from (by
                                          unfold nb077AlphaDummy219;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0236 F I) 0)))) (show
                                        (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy221 x)
                                        from (by
                                          unfold nb077AlphaDummy221;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0238 x) 0))))
                                      (TAlphaVar.there (show (nb077AlphaDummy140 F I) ≠
        (nb077AlphaDummy249 F I) from (by
          unfold nb077AlphaDummy249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0240 F I) 0)))) (show (nb077AlphaDummy143 x) ≠
        (nb077AlphaDummy250 x) from (by
          unfold nb077AlphaDummy250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0241 x) 0)))) (TAlphaVar.there (show
        (nb077AlphaDummy140 F I) ≠ (nb077AlphaDummy223 F I) from (by
          unfold nb077AlphaDummy223;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0237 F I) 0)))) (show (nb077AlphaDummy143 x) ≠
        (nb077AlphaDummy224 x) from (by
          unfold nb077AlphaDummy224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0239 x) 0)))) (TAlphaVar.there (freshVar_injective
        (((synCmpt (nb077AlphaDummy000 F I) (synCvv) (synCplc (Class.cv
        (nb077AlphaDummy000 F I)) (synC1c)))).fv ∪ ((synC1st)).fv) (by decide))
        (freshVar_injective (((synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))).fv ∪
        ((synC1st)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb077AlphaDummy141 F I))).fv ∪
                                        ((Class.cv (nb077AlphaDummy140 F I))).fv)
                                      (by decide)) (freshVar_injective
                                      (((Class.cv (nb077AlphaDummy144 x))).fv ∪
                                        ((Class.cv (nb077AlphaDummy143 x))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077SplitAlpha0029 x F I))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy251 F I), (nb077AlphaDummy252 x)), ((nb077AlphaDummy220 F I),
        (nb077AlphaDummy222 x)), ((nb077AlphaDummy219 F I), (nb077AlphaDummy221 x)),
        ((nb077AlphaDummy249 F I), (nb077AlphaDummy250 x)), ((nb077AlphaDummy223 F I),
        (nb077AlphaDummy224 x)), ((nb077AlphaDummy141 F I), (nb077AlphaDummy144 x)),
        ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I),
        (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
        ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I),
        (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
        (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F I),
        (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I),
        (nb077AlphaDummy018 x F I)), ((nb077AlphaDummy015 F I),
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy001 F I),
        (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy140 F I) ≠ (nb077AlphaDummy220 F I)
                                      from (by
                                        unfold nb077AlphaDummy220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0236 F I) 1)))) (show
                                      (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy222 x) from
                                      (by
                                        unfold nb077AlphaDummy222;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0238 x)
                                                1)))) (TAlphaVar.there (show
                                        (nb077AlphaDummy140 F I) ≠
        (nb077AlphaDummy219 F I) from (by
                                          unfold nb077AlphaDummy219;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0236 F I) 0)))) (show
                                        (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy221 x)
                                        from (by
                                          unfold nb077AlphaDummy221;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0238 x) 0))))
                                      (TAlphaVar.there (show (nb077AlphaDummy140 F I) ≠
        (nb077AlphaDummy249 F I) from (by
          unfold nb077AlphaDummy249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0240 F I) 0)))) (show (nb077AlphaDummy143 x) ≠
        (nb077AlphaDummy250 x) from (by
          unfold nb077AlphaDummy250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0241 x) 0)))) (TAlphaVar.there (show
        (nb077AlphaDummy140 F I) ≠ (nb077AlphaDummy223 F I) from (by
          unfold nb077AlphaDummy223;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0237 F I) 0)))) (show (nb077AlphaDummy143 x) ≠
        (nb077AlphaDummy224 x) from (by
          unfold nb077AlphaDummy224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0239 x) 0)))) (TAlphaVar.there (freshVar_injective
        (((synCmpt (nb077AlphaDummy000 F I) (synCvv) (synCplc (Class.cv
        (nb077AlphaDummy000 F I)) (synC1c)))).fv ∪ ((synC1st)).fv) (by decide))
        (freshVar_injective (((synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))).fv ∪
        ((synC1st)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb077AlphaDummy141 F I))).fv ∪
                                        ((Class.cv (nb077AlphaDummy140 F I))).fv)
                                      (by decide)) (freshVar_injective
                                      (((Class.cv (nb077AlphaDummy144 x))).fv ∪
                                        ((Class.cv (nb077AlphaDummy143 x))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077SplitAlpha0029 x F I))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy251 F I), (nb077AlphaDummy252 x)), ((nb077AlphaDummy220 F I),
        (nb077AlphaDummy222 x)), ((nb077AlphaDummy219 F I), (nb077AlphaDummy221 x)),
        ((nb077AlphaDummy249 F I), (nb077AlphaDummy250 x)), ((nb077AlphaDummy223 F I),
        (nb077AlphaDummy224 x)), ((nb077AlphaDummy141 F I), (nb077AlphaDummy144 x)),
        ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I),
        (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
        ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I),
        (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
        (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F I),
        (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I),
        (nb077AlphaDummy018 x F I)), ((nb077AlphaDummy015 F I),
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy001 F I),
        (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
              (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                        (show (nb077AlphaDummy255 F I) ≠ (nb077AlphaDummy257 F I) from (by
                            unfold nb077AlphaDummy257;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0248 F I) 0))))) (Ne.symm
                        (show (nb077AlphaDummy256 x) ≠ (nb077AlphaDummy258 x) from (by
                            unfold nb077AlphaDummy258;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0249 x) 0)))))
                      (TAlphaVar.there (Ne.symm
                          (show (nb077AlphaDummy000 F I) ≠ (nb077AlphaDummy257 F I) from
                            (by
                              unfold nb077AlphaDummy257;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0246 F I) 0)))))
                        (Ne.symm (show x ≠ (nb077AlphaDummy258 x) from (by
                              unfold nb077AlphaDummy258;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0247 x) 0)))))
                        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb077SplitAlpha0030 x F I)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy255 F I) ≠ (nb077AlphaDummy260 F I) from (by
          unfold nb077AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0280 F I)
                  1)))) (show (nb077AlphaDummy256 x) ≠ (nb077AlphaDummy262 x) from (by
          unfold nb077AlphaDummy262;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0282 x) 1)))) (TAlphaVar.there (show
        (nb077AlphaDummy255 F I) ≠ (nb077AlphaDummy259 F I) from (by
          unfold nb077AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0280 F I)
                  0)))) (show (nb077AlphaDummy256 x) ≠ (nb077AlphaDummy261 x) from (by
          unfold nb077AlphaDummy261;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0282 x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy255 F I) ≠
        (nb077AlphaDummy289 F I) from (by
          unfold nb077AlphaDummy289;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0284 F I)
                  0)))) (show (nb077AlphaDummy256 x) ≠ (nb077AlphaDummy290 x) from (by
          unfold nb077AlphaDummy290;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0285 x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy255 F I) ≠
        (nb077AlphaDummy263 F I) from (by
          unfold nb077AlphaDummy263;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0281 F
                    I)
                  0)))) (show (nb077AlphaDummy256 x) ≠ (nb077AlphaDummy264 x) from (by
          unfold nb077AlphaDummy264;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0283 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy000 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy255 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv x)).fv ∪ ((Class.cv (nb077AlphaDummy256 x))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077SplitAlpha0031 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy291 F I), (nb077AlphaDummy292 x)), ((nb077AlphaDummy260 F I),
        (nb077AlphaDummy262 x)), ((nb077AlphaDummy259 F I), (nb077AlphaDummy261 x)),
        ((nb077AlphaDummy289 F I), (nb077AlphaDummy290 x)), ((nb077AlphaDummy263 F I),
        (nb077AlphaDummy264 x)), ((nb077AlphaDummy255 F I), (nb077AlphaDummy256 x)),
        ((nb077AlphaDummy000 F I), x), ((nb077AlphaDummy257 F I),
        (nb077AlphaDummy258 x)), ((nb077AlphaDummy141 F I), (nb077AlphaDummy144 x)),
        ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I),
        (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
        ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I),
        (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
        (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F I),
        (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I),
        (nb077AlphaDummy018 x F I)), ((nb077AlphaDummy015 F I),
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy001 F I),
        (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn, fv_syn_c0c]))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy255 F I) ≠ (nb077AlphaDummy260 F I) from (by
          unfold nb077AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0280 F I)
                  1)))) (show (nb077AlphaDummy256 x) ≠ (nb077AlphaDummy262 x) from (by
          unfold nb077AlphaDummy262;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0282 x) 1)))) (TAlphaVar.there (show
        (nb077AlphaDummy255 F I) ≠ (nb077AlphaDummy259 F I) from (by
          unfold nb077AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0280 F I)
                  0)))) (show (nb077AlphaDummy256 x) ≠ (nb077AlphaDummy261 x) from (by
          unfold nb077AlphaDummy261;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0282 x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy255 F I) ≠
        (nb077AlphaDummy289 F I) from (by
          unfold nb077AlphaDummy289;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0284 F I)
                  0)))) (show (nb077AlphaDummy256 x) ≠ (nb077AlphaDummy290 x) from (by
          unfold nb077AlphaDummy290;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0285 x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy255 F I) ≠
        (nb077AlphaDummy263 F I) from (by
          unfold nb077AlphaDummy263;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0281 F
                    I)
                  0)))) (show (nb077AlphaDummy256 x) ≠ (nb077AlphaDummy264 x) from (by
          unfold nb077AlphaDummy264;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0283 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy000 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy255 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv x)).fv ∪ ((Class.cv (nb077AlphaDummy256 x))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077SplitAlpha0031 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy291 F I), (nb077AlphaDummy292 x)), ((nb077AlphaDummy260 F I),
        (nb077AlphaDummy262 x)), ((nb077AlphaDummy259 F I), (nb077AlphaDummy261 x)),
        ((nb077AlphaDummy289 F I), (nb077AlphaDummy290 x)), ((nb077AlphaDummy263 F I),
        (nb077AlphaDummy264 x)), ((nb077AlphaDummy255 F I), (nb077AlphaDummy256 x)),
        ((nb077AlphaDummy000 F I), x), ((nb077AlphaDummy257 F I),
        (nb077AlphaDummy258 x)), ((nb077AlphaDummy141 F I), (nb077AlphaDummy144 x)),
        ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I),
        (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
        ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I),
        (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
        (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F I),
        (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I),
        (nb077AlphaDummy018 x F I)), ((nb077AlphaDummy015 F I),
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy001 F I),
        (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb077AlphaDummy000 F I) ≠ (nb077AlphaDummy255 F I) from (by
                            unfold nb077AlphaDummy255;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0250 F I) 0))))
                        (show x ≠ (nb077AlphaDummy256 x) from (by
                            unfold nb077AlphaDummy256;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0251 x) 0))))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                      [((nb077AlphaDummy255 F I), (nb077AlphaDummy256 x)),
                        ((nb077AlphaDummy000 F I), x),
                        ((nb077AlphaDummy257 F I), (nb077AlphaDummy258 x)),
                        ((nb077AlphaDummy141 F I), (nb077AlphaDummy144 x)),
                        ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
                        ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
                        ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
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
                      (synCvv) (by simp only [fv_syn_cvv])))
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy000 F I) ≠
                                    (nb077AlphaDummy296 F I) from (by
                                    unfold nb077AlphaDummy296;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0290 F I)
                                            1)))) (show x ≠ (nb077AlphaDummy299 x) from (by
                                    unfold nb077AlphaDummy299;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0291 x)
                                            1)))) (TAlphaVar.there (show
                                    (nb077AlphaDummy000 F I) ≠ (nb077AlphaDummy295 F I)
                                    from (by
                                      unfold nb077AlphaDummy295;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0290 F I)
                                              0)))) (show x ≠ (nb077AlphaDummy298 x) from (by
                                      unfold nb077AlphaDummy298;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0291 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb077AlphaDummy000 F I) ≠ (nb077AlphaDummy255 F I)
                                      from (by
                                        unfold nb077AlphaDummy255;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0250 F I) 0))))
                                    (show x ≠ (nb077AlphaDummy256 x) from (by
                                        unfold nb077AlphaDummy256;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0251 x)
                                                0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                            (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed [((nb077AlphaDummy297 F I),
                                      (nb077AlphaDummy300 x)), ((nb077AlphaDummy296 F I),
                                      (nb077AlphaDummy299 x)), ((nb077AlphaDummy295 F I),
                                      (nb077AlphaDummy298 x)), ((nb077AlphaDummy255 F I),
                                      (nb077AlphaDummy256 x)),
                                    ((nb077AlphaDummy000 F I), x),
                                    ((nb077AlphaDummy257 F I), (nb077AlphaDummy258 x)),
                                    ((nb077AlphaDummy141 F I), (nb077AlphaDummy144 x)),
                                    ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
                                    ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
                                    ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
                                    ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                                    ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                                    ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                                    ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                                    ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                                    ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                                    ((nb077AlphaDummy016 F I),
                                      (nb077AlphaDummy018 x F I)),
                                    ((nb077AlphaDummy015 F I),
                                      (nb077AlphaDummy017 x F I)),
                                    ((nb077AlphaDummy001 F I),
                                      (nb077AlphaDummy002 x F I)),
                                    ((nb077AlphaDummy004 F I),
                                      (nb077AlphaDummy006 x F I)),
                                    ((nb077AlphaDummy003 F I),
                                      (nb077AlphaDummy005 x F I))]
                                  (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy296 F I) ≠ (nb077AlphaDummy303 F I) from
        (by
          unfold nb077AlphaDummy303;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0294
                    F I)
                  0)))) (show (nb077AlphaDummy299 x) ≠ (nb077AlphaDummy304 x) from (by
          unfold nb077AlphaDummy304;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0295
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy296 F I) ≠
        (nb077AlphaDummy301 F I) from (by
          unfold nb077AlphaDummy301;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0292
                    F I)
                  0)))) (show (nb077AlphaDummy299 x) ≠ (nb077AlphaDummy302 x) from (by
          unfold nb077AlphaDummy302;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0293
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy000 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv x)).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy297 F I) ≠ (nb077AlphaDummy303 F I) from
        (by
          unfold nb077AlphaDummy303;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0298
                    F I)
                  0)))) (show (nb077AlphaDummy300 x) ≠ (nb077AlphaDummy304 x) from (by
          unfold nb077AlphaDummy304;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0299
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy297 F I) ≠
        (nb077AlphaDummy301 F I) from (by
          unfold nb077AlphaDummy301;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0296
                    F I)
                  0)))) (show (nb077AlphaDummy300 x) ≠ (nb077AlphaDummy302 x) from (by
          unfold nb077AlphaDummy302;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0297
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy296 F I) ≠ (nb077AlphaDummy303 F I) from
        (by
          unfold nb077AlphaDummy303;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0294
                    F I)
                  0)))) (show (nb077AlphaDummy299 x) ≠ (nb077AlphaDummy304 x) from (by
          unfold nb077AlphaDummy304;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0295
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy296 F I) ≠
        (nb077AlphaDummy301 F I) from (by
          unfold nb077AlphaDummy301;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0292
                    F I)
                  0)))) (show (nb077AlphaDummy299 x) ≠ (nb077AlphaDummy302 x) from (by
          unfold nb077AlphaDummy302;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0293
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy000 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv x)).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy297 F I) ≠ (nb077AlphaDummy303 F I) from
        (by
          unfold nb077AlphaDummy303;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0298
                    F I)
                  0)))) (show (nb077AlphaDummy300 x) ≠ (nb077AlphaDummy304 x) from (by
          unfold nb077AlphaDummy304;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0299
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy297 F I) ≠
        (nb077AlphaDummy301 F I) from (by
          unfold nb077AlphaDummy301;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0296
                    F I)
                  0)))) (show (nb077AlphaDummy300 x) ≠ (nb077AlphaDummy302 x) from (by
          unfold nb077AlphaDummy302;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0297
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                    [((nb077AlphaDummy297 F I), (nb077AlphaDummy300 x)),
                                      ((nb077AlphaDummy296 F I), (nb077AlphaDummy299 x)),
                                      ((nb077AlphaDummy295 F I), (nb077AlphaDummy298 x)),
                                      ((nb077AlphaDummy255 F I), (nb077AlphaDummy256 x)),
                                      ((nb077AlphaDummy000 F I), x),
                                      ((nb077AlphaDummy257 F I), (nb077AlphaDummy258 x)),
                                      ((nb077AlphaDummy141 F I), (nb077AlphaDummy144 x)),
                                      ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
                                      ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
                                      ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
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
                                      ((nb077AlphaDummy001 F I),
                                        (nb077AlphaDummy002 x F I)),
                                      ((nb077AlphaDummy004 F I),
                                        (nb077AlphaDummy006 x F I)),
                                      ((nb077AlphaDummy003 F I),
                                        (nb077AlphaDummy005 x F I))]
                                    (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                  (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                        (((Class.cv (nb077AlphaDummy000 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
                                        (((Class.cv x)).fv ∪ ((synC1c)).fv) (by decide))
                                      (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077AlphaDummy000 F I))).fv ∪ ((synC1c)).fv) (by decide))
                                        (freshVar_injective (((Class.cv x)).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy296 F I) ≠ (nb077AlphaDummy307 F I) from
        (by
          unfold nb077AlphaDummy307;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0302
                    F I)
                  0)))) (show (nb077AlphaDummy299 x) ≠ (nb077AlphaDummy308 x) from (by
          unfold nb077AlphaDummy308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0303
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy296 F I) ≠
        (nb077AlphaDummy305 F I) from (by
          unfold nb077AlphaDummy305;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0300
                    F I)
                  0)))) (show (nb077AlphaDummy299 x) ≠ (nb077AlphaDummy306 x) from (by
          unfold nb077AlphaDummy306;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0301
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy000 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv x)).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy296 F I) ≠ (nb077AlphaDummy307 F I) from
        (by
          unfold nb077AlphaDummy307;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0302
                    F I)
                  0)))) (show (nb077AlphaDummy299 x) ≠ (nb077AlphaDummy308 x) from (by
          unfold nb077AlphaDummy308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0303
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy296 F I) ≠
        (nb077AlphaDummy305 F I) from (by
          unfold nb077AlphaDummy305;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0300
                    F I)
                  0)))) (show (nb077AlphaDummy299 x) ≠ (nb077AlphaDummy306 x) from (by
          unfold nb077AlphaDummy306;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0301
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy000 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv x)).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))))
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy297 F I) ≠ (nb077AlphaDummy309 F I) from
        (by
          unfold nb077AlphaDummy309;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0306
                    F I)
                  0)))) (show (nb077AlphaDummy300 x) ≠ (nb077AlphaDummy310 x) from (by
          unfold nb077AlphaDummy310;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0307
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy297 F I) ≠
        (nb077AlphaDummy305 F I) from (by
          unfold nb077AlphaDummy305;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0304
                    F I)
                  0)))) (show (nb077AlphaDummy300 x) ≠ (nb077AlphaDummy306 x) from (by
          unfold nb077AlphaDummy306;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0305
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy297 F I) ≠ (nb077AlphaDummy309 F I) from (by
          unfold nb077AlphaDummy309;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0306
                    F I)
                  0)))) (show (nb077AlphaDummy300 x) ≠ (nb077AlphaDummy310 x) from (by
          unfold nb077AlphaDummy310;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0307
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy297 F I) ≠
        (nb077AlphaDummy305 F I) from (by
          unfold nb077AlphaDummy305;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0304
                    F I)
                  0)))) (show (nb077AlphaDummy300 x) ≠ (nb077AlphaDummy306 x) from (by
          unfold nb077AlphaDummy306;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0305
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part047`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb077_split_alpha_0033`. -/
@[expose]
noncomputable def nb077SplitAlpha0033 (x : Var) (F : Class) (I : Class) :
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
                                      ((nb077AlphaDummy001 F I),
                                        (nb077AlphaDummy002 x F I)),
                                      ((nb077AlphaDummy004 F I),
                                        (nb077AlphaDummy006 x F I)),
                                      ((nb077AlphaDummy003 F I),
                                        (nb077AlphaDummy005 x F I))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
