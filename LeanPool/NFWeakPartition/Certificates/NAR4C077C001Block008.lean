/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C077C001Block007

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C077C001Part022`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb077_split_alpha_0010`. -/
@[expose]
noncomputable def nb077SplitAlpha0010 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077AlphaDummy225 F I), (nb077AlphaDummy226 x)),
        ((nb077AlphaDummy223 F I), (nb077AlphaDummy224 x)),
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
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy225 F I))
          (Class.cab (nb077AlphaDummy219 F I)
            (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy141 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                (synCphi (Class.cv (nb077AlphaDummy220 F I))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy225 F I))
            (Class.cab (nb077AlphaDummy219 F I)
              (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy141 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                  (synCphi (Class.cv (nb077AlphaDummy220 F I)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy226 x))
          (Class.cab (nb077AlphaDummy221 x)
            (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy144 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                (synCphi (Class.cv (nb077AlphaDummy222 x))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy226 x))
            (Class.cab (nb077AlphaDummy221 x)
              (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy144 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                  (synCphi (Class.cv (nb077AlphaDummy222 x))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077AlphaDummy141 F I) ≠ (nb077AlphaDummy220 F I) from (by
                      unfold nb077AlphaDummy220;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0208 F I) 1))))
                  (show (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy222 x) from (by
                      unfold nb077AlphaDummy222;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0210 x) 1))))
                  (TAlphaVar.there
                    (show (nb077AlphaDummy141 F I) ≠ (nb077AlphaDummy219 F I) from (by
                        unfold nb077AlphaDummy219;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0208 F I) 0))))
                    (show (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy221 x) from (by
                        unfold nb077AlphaDummy221;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0210 x) 0)))) (TAlphaVar.there
                      (show (nb077AlphaDummy141 F I) ≠ (nb077AlphaDummy225 F I) from (by
                          unfold nb077AlphaDummy225;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0212 F I) 0))))
                      (show (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy226 x) from (by
                          unfold nb077AlphaDummy226;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0213 x) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy141 F I) ≠ (nb077AlphaDummy223 F I) from (by
                            unfold nb077AlphaDummy223;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0209 F I) 0))))
                        (show (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy224 x) from (by
                            unfold nb077AlphaDummy224;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0211 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb077AlphaDummy141 F I))).fv ∪
                      ((Class.cv (nb077AlphaDummy140 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077AlphaDummy144 x))).fv ∪
                      ((Class.cv (nb077AlphaDummy143 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077AlphaDummy220 F I) ≠ (nb077AlphaDummy227 F I) from
                            (by
                              unfold nb077AlphaDummy227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0214 F I) 0))))
                          (show (nb077AlphaDummy222 x) ≠ (nb077AlphaDummy229 x) from (by
                              unfold nb077AlphaDummy229;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0215 x) 0))))
                          (TAlphaVar.there (show
                              (nb077AlphaDummy220 F I) ≠ (nb077AlphaDummy228 F I) from (by
                                unfold nb077AlphaDummy228;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0214 F I) 1))))
                            (show (nb077AlphaDummy222 x) ≠ (nb077AlphaDummy230 x) from (by
                                unfold nb077AlphaDummy230;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0215 x) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb077AlphaDummy220 F I))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb077AlphaDummy222 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy227 F I) ≠ (nb077AlphaDummy234 F I) from
        (by
          unfold nb077AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0218 F I) 1)))) (show (nb077AlphaDummy229 x) ≠
        (nb077AlphaDummy237 x) from (by
          unfold nb077AlphaDummy237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0219 x) 1)))) (TAlphaVar.there (show
        (nb077AlphaDummy227 F I) ≠ (nb077AlphaDummy233 F I) from (by
          unfold nb077AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0218 F I)
                  0)))) (show (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy236 x) from (by
          unfold nb077AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0219 x) 0)))) (TAlphaVar.there (show
        (nb077AlphaDummy227 F I) ≠ (nb077AlphaDummy231 F I) from (by
          unfold nb077AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0216 F I)
                  0)))) (show (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy232 x) from (by
          unfold nb077AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0217 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy235 F I), (nb077AlphaDummy238 x)), ((nb077AlphaDummy234 F I),
        (nb077AlphaDummy237 x)), ((nb077AlphaDummy233 F I), (nb077AlphaDummy236 x)),
        ((nb077AlphaDummy231 F I), (nb077AlphaDummy232 x)), ((nb077AlphaDummy227 F I),
        (nb077AlphaDummy229 x)), ((nb077AlphaDummy228 F I), (nb077AlphaDummy230 x)),
        ((nb077AlphaDummy220 F I), (nb077AlphaDummy222 x)), ((nb077AlphaDummy219 F I),
        (nb077AlphaDummy221 x)), ((nb077AlphaDummy225 F I), (nb077AlphaDummy226 x)),
        ((nb077AlphaDummy223 F I), (nb077AlphaDummy224 x)), ((nb077AlphaDummy141 F I),
        (nb077AlphaDummy144 x)), ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
        ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I),
        (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
        (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
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
        (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠ (nb077AlphaDummy241 F I) from
        (by
          unfold
            nb077AlphaDummy241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0222
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy242 x) from (by
          unfold
            nb077AlphaDummy242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0223
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠
        (nb077AlphaDummy239 F I) from (by
          unfold
            nb077AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0220
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy240 x) from (by
          unfold
            nb077AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0221
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy227
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠ (nb077AlphaDummy241 F I) from
        (by
          unfold
            nb077AlphaDummy241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0226
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy242 x) from (by
          unfold
            nb077AlphaDummy242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0227
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠
        (nb077AlphaDummy239 F I) from (by
          unfold
            nb077AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0224
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy240 x) from (by
          unfold
            nb077AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0225
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠ (nb077AlphaDummy241 F I) from
        (by
          unfold
            nb077AlphaDummy241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0222
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy242 x) from (by
          unfold
            nb077AlphaDummy242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0223
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠
        (nb077AlphaDummy239 F I) from (by
          unfold
            nb077AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0220
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy240 x) from (by
          unfold
            nb077AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0221
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy227
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠ (nb077AlphaDummy241 F I) from
        (by
          unfold
            nb077AlphaDummy241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0226
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy242 x) from (by
          unfold
            nb077AlphaDummy242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0227
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠
        (nb077AlphaDummy239 F I) from (by
          unfold
            nb077AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0224
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy240 x) from (by
          unfold
            nb077AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0225
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy235 F I), (nb077AlphaDummy238 x)), ((nb077AlphaDummy234 F I),
        (nb077AlphaDummy237 x)), ((nb077AlphaDummy233 F I), (nb077AlphaDummy236 x)),
        ((nb077AlphaDummy231 F I), (nb077AlphaDummy232 x)), ((nb077AlphaDummy227 F I),
        (nb077AlphaDummy229 x)), ((nb077AlphaDummy228 F I), (nb077AlphaDummy230 x)),
        ((nb077AlphaDummy220 F I), (nb077AlphaDummy222 x)), ((nb077AlphaDummy219 F I),
        (nb077AlphaDummy221 x)), ((nb077AlphaDummy225 F I), (nb077AlphaDummy226 x)),
        ((nb077AlphaDummy223 F I), (nb077AlphaDummy224 x)), ((nb077AlphaDummy141 F I),
        (nb077AlphaDummy144 x)), ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
        ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I),
        (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
        (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy227 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb077AlphaDummy227 F I))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb077AlphaDummy229 x))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy234
        F I) ≠ (nb077AlphaDummy245 F I) from (by
          unfold
            nb077AlphaDummy245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0230
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy246 x) from (by
          unfold
            nb077AlphaDummy246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0231
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠
        (nb077AlphaDummy243 F I) from (by
          unfold
            nb077AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0228
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy244 x) from (by
          unfold
            nb077AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0229
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy227
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠ (nb077AlphaDummy245 F I) from
        (by
          unfold
            nb077AlphaDummy245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0230
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy246 x) from (by
          unfold
            nb077AlphaDummy246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0231
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠
        (nb077AlphaDummy243 F I) from (by
          unfold
            nb077AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0228
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy244 x) from (by
          unfold
            nb077AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0229
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy227
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy235
        F I) ≠ (nb077AlphaDummy247 F I) from (by
          unfold
            nb077AlphaDummy247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0234
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy248 x) from (by
          unfold
            nb077AlphaDummy248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0235
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠
        (nb077AlphaDummy243 F I) from (by
          unfold
            nb077AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0232
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy244 x) from (by
          unfold
            nb077AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0233
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy235
        F I) ≠ (nb077AlphaDummy247 F I) from (by
          unfold
            nb077AlphaDummy247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0234
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy248 x) from (by
          unfold
            nb077AlphaDummy248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0235
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠
        (nb077AlphaDummy243 F I) from (by
          unfold
            nb077AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0232
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy244 x) from (by
          unfold
            nb077AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0233
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy227 F I) ≠ (nb077AlphaDummy231 F I)
                                      from (by
                                        unfold nb077AlphaDummy231;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0216 F I) 0)))) (show
                                      (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy232 x) from
                                      (by
                                        unfold nb077AlphaDummy232;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0217 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed [((nb077AlphaDummy231 F I),
                                      (nb077AlphaDummy232 x)), ((nb077AlphaDummy227 F I),
                                      (nb077AlphaDummy229 x)), ((nb077AlphaDummy228 F I),
                                      (nb077AlphaDummy230 x)), ((nb077AlphaDummy220 F I),
                                      (nb077AlphaDummy222 x)), ((nb077AlphaDummy219 F I),
                                      (nb077AlphaDummy221 x)), ((nb077AlphaDummy225 F I),
                                      (nb077AlphaDummy226 x)), ((nb077AlphaDummy223 F I),
                                      (nb077AlphaDummy224 x)), ((nb077AlphaDummy141 F I),
                                      (nb077AlphaDummy144 x)), ((nb077AlphaDummy140 F I),
                                      (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I),
                                      (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I),
                                      (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I),
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
                                    (nb077AlphaDummy227 F I) ≠ (nb077AlphaDummy231 F I)
                                    from (by
                                      unfold nb077AlphaDummy231;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0216 F I)
                                              0)))) (show
                                    (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy232 x) from
                                    (by
                                      unfold nb077AlphaDummy232;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0217 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy227 F I) ≠ (nb077AlphaDummy231 F I)
                                      from (by
                                        unfold nb077AlphaDummy231;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0216 F I) 0)))) (show
                                      (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy232 x) from
                                      (by
                                        unfold nb077AlphaDummy232;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0217 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed [((nb077AlphaDummy231 F I),
                                      (nb077AlphaDummy232 x)), ((nb077AlphaDummy227 F I),
                                      (nb077AlphaDummy229 x)), ((nb077AlphaDummy228 F I),
                                      (nb077AlphaDummy230 x)), ((nb077AlphaDummy220 F I),
                                      (nb077AlphaDummy222 x)), ((nb077AlphaDummy219 F I),
                                      (nb077AlphaDummy221 x)), ((nb077AlphaDummy225 F I),
                                      (nb077AlphaDummy226 x)), ((nb077AlphaDummy223 F I),
                                      (nb077AlphaDummy224 x)), ((nb077AlphaDummy141 F I),
                                      (nb077AlphaDummy144 x)), ((nb077AlphaDummy140 F I),
                                      (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I),
                                      (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I),
                                      (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I),
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
                    (show (nb077AlphaDummy141 F I) ≠ (nb077AlphaDummy220 F I) from (by
                        unfold nb077AlphaDummy220;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0208 F I) 1))))
                    (show (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy222 x) from (by
                        unfold nb077AlphaDummy222;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0210 x) 1)))) (TAlphaVar.there
                      (show (nb077AlphaDummy141 F I) ≠ (nb077AlphaDummy219 F I) from (by
                          unfold nb077AlphaDummy219;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0208 F I) 0))))
                      (show (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy221 x) from (by
                          unfold nb077AlphaDummy221;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0210 x) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy141 F I) ≠ (nb077AlphaDummy225 F I) from (by
                            unfold nb077AlphaDummy225;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0212 F I) 0))))
                        (show (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy226 x) from (by
                            unfold nb077AlphaDummy226;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0213 x) 0))))
                        (TAlphaVar.there
                          (show (nb077AlphaDummy141 F I) ≠ (nb077AlphaDummy223 F I) from
                            (by
                              unfold nb077AlphaDummy223;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0209 F I) 0))))
                          (show (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy224 x) from (by
                              unfold nb077AlphaDummy224;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0211 x) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb077AlphaDummy141 F I))).fv ∪
                        ((Class.cv (nb077AlphaDummy140 F I))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb077AlphaDummy144 x))).fv ∪
                        ((Class.cv (nb077AlphaDummy143 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy220 F I) ≠ (nb077AlphaDummy227 F I) from (by
                                unfold nb077AlphaDummy227;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0214 F I) 0))))
                            (show (nb077AlphaDummy222 x) ≠ (nb077AlphaDummy229 x) from (by
                                unfold nb077AlphaDummy229;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0215 x) 0))))
                            (TAlphaVar.there (show
                                (nb077AlphaDummy220 F I) ≠ (nb077AlphaDummy228 F I) from
                                (by
                                  unfold nb077AlphaDummy228;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0214 F I)
                                          1))))
                              (show (nb077AlphaDummy222 x) ≠ (nb077AlphaDummy230 x) from
                                (by
                                  unfold nb077AlphaDummy230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0215 x) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb077AlphaDummy220 F I))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb077AlphaDummy222 x))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy227 F I) ≠ (nb077AlphaDummy234 F I) from (by
          unfold nb077AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0218 F I)
                  1)))) (show (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy237 x) from (by
          unfold nb077AlphaDummy237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0219 x) 1)))) (TAlphaVar.there (show
        (nb077AlphaDummy227 F I) ≠ (nb077AlphaDummy233 F I) from (by
          unfold nb077AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0218 F I)
                  0)))) (show (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy236 x) from (by
          unfold nb077AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0219 x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy227 F I) ≠
        (nb077AlphaDummy231 F I) from (by
          unfold nb077AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0216 F I)
                  0)))) (show (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy232 x) from (by
          unfold nb077AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0217 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy235 F I), (nb077AlphaDummy238 x)), ((nb077AlphaDummy234 F I),
        (nb077AlphaDummy237 x)), ((nb077AlphaDummy233 F I), (nb077AlphaDummy236 x)),
        ((nb077AlphaDummy231 F I), (nb077AlphaDummy232 x)), ((nb077AlphaDummy227 F I),
        (nb077AlphaDummy229 x)), ((nb077AlphaDummy228 F I), (nb077AlphaDummy230 x)),
        ((nb077AlphaDummy220 F I), (nb077AlphaDummy222 x)), ((nb077AlphaDummy219 F I),
        (nb077AlphaDummy221 x)), ((nb077AlphaDummy225 F I), (nb077AlphaDummy226 x)),
        ((nb077AlphaDummy223 F I), (nb077AlphaDummy224 x)), ((nb077AlphaDummy141 F I),
        (nb077AlphaDummy144 x)), ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
        ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I),
        (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
        (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
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
        (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠ (nb077AlphaDummy241 F I) from
        (by
          unfold
            nb077AlphaDummy241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0222
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy242 x) from (by
          unfold
            nb077AlphaDummy242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0223
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠
        (nb077AlphaDummy239 F I) from (by
          unfold
            nb077AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0220
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy240 x) from (by
          unfold
            nb077AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0221
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy227
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠ (nb077AlphaDummy241 F I) from
        (by
          unfold
            nb077AlphaDummy241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0226
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy242 x) from (by
          unfold
            nb077AlphaDummy242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0227
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠
        (nb077AlphaDummy239 F I) from (by
          unfold
            nb077AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0224
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy240 x) from (by
          unfold
            nb077AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0225
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠ (nb077AlphaDummy241 F I) from
        (by
          unfold
            nb077AlphaDummy241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0222
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy242 x) from (by
          unfold
            nb077AlphaDummy242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0223
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠
        (nb077AlphaDummy239 F I) from (by
          unfold
            nb077AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0220
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy240 x) from (by
          unfold
            nb077AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0221
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy227
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠ (nb077AlphaDummy241 F I) from
        (by
          unfold
            nb077AlphaDummy241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0226
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy242 x) from (by
          unfold
            nb077AlphaDummy242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0227
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠
        (nb077AlphaDummy239 F I) from (by
          unfold
            nb077AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0224
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy240 x) from (by
          unfold
            nb077AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0225
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy235 F I), (nb077AlphaDummy238 x)), ((nb077AlphaDummy234 F I),
        (nb077AlphaDummy237 x)), ((nb077AlphaDummy233 F I), (nb077AlphaDummy236 x)),
        ((nb077AlphaDummy231 F I), (nb077AlphaDummy232 x)), ((nb077AlphaDummy227 F I),
        (nb077AlphaDummy229 x)), ((nb077AlphaDummy228 F I), (nb077AlphaDummy230 x)),
        ((nb077AlphaDummy220 F I), (nb077AlphaDummy222 x)), ((nb077AlphaDummy219 F I),
        (nb077AlphaDummy221 x)), ((nb077AlphaDummy225 F I), (nb077AlphaDummy226 x)),
        ((nb077AlphaDummy223 F I), (nb077AlphaDummy224 x)), ((nb077AlphaDummy141 F I),
        (nb077AlphaDummy144 x)), ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
        ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I),
        (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
        (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy227 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077AlphaDummy229
        x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy227 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy234
        F I) ≠ (nb077AlphaDummy245 F I) from (by
          unfold
            nb077AlphaDummy245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0230
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy246 x) from (by
          unfold
            nb077AlphaDummy246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0231
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠
        (nb077AlphaDummy243 F I) from (by
          unfold
            nb077AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0228
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy244 x) from (by
          unfold
            nb077AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0229
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy227
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠ (nb077AlphaDummy245 F I) from
        (by
          unfold
            nb077AlphaDummy245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0230
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy246 x) from (by
          unfold
            nb077AlphaDummy246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0231
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠
        (nb077AlphaDummy243 F I) from (by
          unfold
            nb077AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0228
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy244 x) from (by
          unfold
            nb077AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0229
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy227
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy235
        F I) ≠ (nb077AlphaDummy247 F I) from (by
          unfold
            nb077AlphaDummy247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0234
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy248 x) from (by
          unfold
            nb077AlphaDummy248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0235
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠
        (nb077AlphaDummy243 F I) from (by
          unfold
            nb077AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0232
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy244 x) from (by
          unfold
            nb077AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0233
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy235
        F I) ≠ (nb077AlphaDummy247 F I) from (by
          unfold
            nb077AlphaDummy247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0234
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy248 x) from (by
          unfold
            nb077AlphaDummy248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0235
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠
        (nb077AlphaDummy243 F I) from (by
          unfold
            nb077AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0232
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy244 x) from (by
          unfold
            nb077AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0233
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077AlphaDummy227 F I) ≠
        (nb077AlphaDummy231 F I) from (by
                                          unfold nb077AlphaDummy231;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0216 F I) 0)))) (show
                                        (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy232 x)
                                        from (by
                                          unfold nb077AlphaDummy232;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0217 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb077AlphaDummy231 F I), (nb077AlphaDummy232 x)),
                                      ((nb077AlphaDummy227 F I), (nb077AlphaDummy229 x)),
                                      ((nb077AlphaDummy228 F I), (nb077AlphaDummy230 x)),
                                      ((nb077AlphaDummy220 F I), (nb077AlphaDummy222 x)),
                                      ((nb077AlphaDummy219 F I), (nb077AlphaDummy221 x)),
                                      ((nb077AlphaDummy225 F I), (nb077AlphaDummy226 x)),
                                      ((nb077AlphaDummy223 F I), (nb077AlphaDummy224 x)),
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
                                      (nb077AlphaDummy227 F I) ≠ (nb077AlphaDummy231 F I)
                                      from (by
                                        unfold nb077AlphaDummy231;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0216 F I) 0)))) (show
                                      (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy232 x) from
                                      (by
                                        unfold nb077AlphaDummy232;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0217 x)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077AlphaDummy227 F I) ≠
        (nb077AlphaDummy231 F I) from (by
                                          unfold nb077AlphaDummy231;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0216 F I) 0)))) (show
                                        (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy232 x)
                                        from (by
                                          unfold nb077AlphaDummy232;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0217 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb077AlphaDummy231 F I), (nb077AlphaDummy232 x)),
                                      ((nb077AlphaDummy227 F I), (nb077AlphaDummy229 x)),
                                      ((nb077AlphaDummy228 F I), (nb077AlphaDummy230 x)),
                                      ((nb077AlphaDummy220 F I), (nb077AlphaDummy222 x)),
                                      ((nb077AlphaDummy219 F I), (nb077AlphaDummy221 x)),
                                      ((nb077AlphaDummy225 F I), (nb077AlphaDummy226 x)),
                                      ((nb077AlphaDummy223 F I), (nb077AlphaDummy224 x)),
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

/-! Certificates from `NAR4C077C001Part023`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb077_split_alpha_0011`. -/
@[expose]
noncomputable def nb077SplitAlpha0011 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077AlphaDummy253 F I), (nb077AlphaDummy254 x)),
        ((nb077AlphaDummy251 F I), (nb077AlphaDummy252 x)),
        ((nb077AlphaDummy220 F I), (nb077AlphaDummy222 x)),
        ((nb077AlphaDummy219 F I), (nb077AlphaDummy221 x)),
        ((nb077AlphaDummy249 F I), (nb077AlphaDummy250 x)),
        ((nb077AlphaDummy223 F I), (nb077AlphaDummy224 x)),
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
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy253 F I))
          (synCphi (Class.cv (nb077AlphaDummy220 F I)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy253 F I))
            (synCphi (Class.cv (nb077AlphaDummy220 F I))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy254 x))
          (synCphi (Class.cv (nb077AlphaDummy222 x)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy254 x))
            (synCphi (Class.cv (nb077AlphaDummy222 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077AlphaDummy220 F I) ≠ (nb077AlphaDummy227 F I) from (by
                      unfold nb077AlphaDummy227;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0214 F I) 0))))
                  (show (nb077AlphaDummy222 x) ≠ (nb077AlphaDummy229 x) from (by
                      unfold nb077AlphaDummy229;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0215 x) 0))))
                  (TAlphaVar.there
                    (show (nb077AlphaDummy220 F I) ≠ (nb077AlphaDummy228 F I) from (by
                        unfold nb077AlphaDummy228;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0214 F I) 1))))
                    (show (nb077AlphaDummy222 x) ≠ (nb077AlphaDummy230 x) from (by
                        unfold nb077AlphaDummy230;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0215 x) 1)))) (TAlphaVar.there
                      (show (nb077AlphaDummy220 F I) ≠ (nb077AlphaDummy253 F I) from (by
                          unfold nb077AlphaDummy253;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0244 F I) 0))))
                      (show (nb077AlphaDummy222 x) ≠ (nb077AlphaDummy254 x) from (by
                          unfold nb077AlphaDummy254;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0245 x) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy220 F I) ≠ (nb077AlphaDummy251 F I) from (by
                            unfold nb077AlphaDummy251;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0242 F I) 0))))
                        (show (nb077AlphaDummy222 x) ≠ (nb077AlphaDummy252 x) from (by
                            unfold nb077AlphaDummy252;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0243 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb077AlphaDummy220 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077AlphaDummy222 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy227 F I) ≠ (nb077AlphaDummy234 F I)
                                      from (by
                                        unfold nb077AlphaDummy234;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0218 F I) 1)))) (show
                                      (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy237 x) from
                                      (by
                                        unfold nb077AlphaDummy237;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0219 x)
                                                1)))) (TAlphaVar.there (show
                                        (nb077AlphaDummy227 F I) ≠
        (nb077AlphaDummy233 F I) from (by
                                          unfold nb077AlphaDummy233;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0218 F I) 0)))) (show
                                        (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy236 x)
                                        from (by
                                          unfold nb077AlphaDummy236;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0219 x) 0))))
                                      (TAlphaVar.there (show (nb077AlphaDummy227 F I) ≠
        (nb077AlphaDummy231 F I) from (by
          unfold nb077AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0216 F I) 0)))) (show (nb077AlphaDummy229 x) ≠
        (nb077AlphaDummy232 x) from (by
          unfold nb077AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0217 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb077AlphaDummy235 F I),
        (nb077AlphaDummy238 x)), ((nb077AlphaDummy234 F I), (nb077AlphaDummy237 x)),
                                        ((nb077AlphaDummy233 F I),
        (nb077AlphaDummy236 x)), ((nb077AlphaDummy231 F I), (nb077AlphaDummy232 x)),
                                        ((nb077AlphaDummy227 F I),
        (nb077AlphaDummy229 x)), ((nb077AlphaDummy228 F I), (nb077AlphaDummy230 x)),
                                        ((nb077AlphaDummy253 F I),
        (nb077AlphaDummy254 x)), ((nb077AlphaDummy251 F I), (nb077AlphaDummy252 x)),
                                        ((nb077AlphaDummy220 F I),
        (nb077AlphaDummy222 x)), ((nb077AlphaDummy219 F I), (nb077AlphaDummy221 x)),
                                        ((nb077AlphaDummy249 F I),
        (nb077AlphaDummy250 x)), ((nb077AlphaDummy223 F I), (nb077AlphaDummy224 x)),
                                        ((nb077AlphaDummy141 F I),
        (nb077AlphaDummy144 x)), ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
                                        ((nb077AlphaDummy139 F I),
        (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
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
        (nb077AlphaDummy234 F I) ≠ (nb077AlphaDummy241 F I) from (by
          unfold
            nb077AlphaDummy241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0222
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy242 x) from (by
          unfold
            nb077AlphaDummy242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0223
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠
        (nb077AlphaDummy239 F I) from (by
          unfold
            nb077AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0220
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy240 x) from (by
          unfold
            nb077AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0221
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy227
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠
        (nb077AlphaDummy241 F I) from (by
          unfold
            nb077AlphaDummy241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0226
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy242 x) from (by
          unfold
            nb077AlphaDummy242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0227
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠
        (nb077AlphaDummy239 F I) from (by
          unfold
            nb077AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0224
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy240 x) from (by
          unfold
            nb077AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0225
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠ (nb077AlphaDummy241 F I) from
        (by
          unfold
            nb077AlphaDummy241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0222
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy242 x) from (by
          unfold
            nb077AlphaDummy242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0223
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠
        (nb077AlphaDummy239 F I) from (by
          unfold
            nb077AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0220
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy240 x) from (by
          unfold
            nb077AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0221
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy227
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠
        (nb077AlphaDummy241 F I) from (by
          unfold
            nb077AlphaDummy241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0226
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy242 x) from (by
          unfold
            nb077AlphaDummy242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0227
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠
        (nb077AlphaDummy239 F I) from (by
          unfold
            nb077AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0224
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy240 x) from (by
          unfold
            nb077AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0225
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb077AlphaDummy235 F I),
        (nb077AlphaDummy238 x)), ((nb077AlphaDummy234 F I), (nb077AlphaDummy237 x)),
        ((nb077AlphaDummy233 F I), (nb077AlphaDummy236 x)), ((nb077AlphaDummy231 F I),
        (nb077AlphaDummy232 x)), ((nb077AlphaDummy227 F I), (nb077AlphaDummy229 x)),
        ((nb077AlphaDummy228 F I), (nb077AlphaDummy230 x)), ((nb077AlphaDummy253 F I),
        (nb077AlphaDummy254 x)), ((nb077AlphaDummy251 F I), (nb077AlphaDummy252 x)),
        ((nb077AlphaDummy220 F I), (nb077AlphaDummy222 x)), ((nb077AlphaDummy219 F I),
        (nb077AlphaDummy221 x)), ((nb077AlphaDummy249 F I), (nb077AlphaDummy250 x)),
        ((nb077AlphaDummy223 F I), (nb077AlphaDummy224 x)), ((nb077AlphaDummy141 F I),
        (nb077AlphaDummy144 x)), ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
        ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I),
        (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
        (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
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
        (((Class.cv (nb077AlphaDummy227 F I))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy227 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy234 F I) ≠ (nb077AlphaDummy245 F I) from (by
          unfold
            nb077AlphaDummy245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0230
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy246 x) from (by
          unfold
            nb077AlphaDummy246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0231
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠
        (nb077AlphaDummy243 F I) from (by
          unfold
            nb077AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0228
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy244 x) from (by
          unfold
            nb077AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0229
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy227
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠
        (nb077AlphaDummy245 F I) from (by
          unfold
            nb077AlphaDummy245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0230
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy246 x) from (by
          unfold
            nb077AlphaDummy246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0231
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠
        (nb077AlphaDummy243 F I) from (by
          unfold
            nb077AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0228
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy244 x) from (by
          unfold
            nb077AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0229
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy227
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy235 F I) ≠ (nb077AlphaDummy247 F I) from (by
          unfold
            nb077AlphaDummy247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0234
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy248 x) from (by
          unfold
            nb077AlphaDummy248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0235
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠
        (nb077AlphaDummy243 F I) from (by
          unfold
            nb077AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0232
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy244 x) from (by
          unfold
            nb077AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0233
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy235 F I) ≠ (nb077AlphaDummy247 F I) from (by
          unfold
            nb077AlphaDummy247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0234
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy248 x) from (by
          unfold
            nb077AlphaDummy248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0235
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠
        (nb077AlphaDummy243 F I) from (by
          unfold
            nb077AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0232
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy244 x) from (by
          unfold
            nb077AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0233
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy227 F I) ≠ (nb077AlphaDummy231 F I) from (by
                                unfold nb077AlphaDummy231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0216 F I) 0))))
                            (show (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy232 x) from (by
                                unfold nb077AlphaDummy232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0217 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb077AlphaDummy231 F I), (nb077AlphaDummy232 x)),
                            ((nb077AlphaDummy227 F I), (nb077AlphaDummy229 x)),
                            ((nb077AlphaDummy228 F I), (nb077AlphaDummy230 x)),
                            ((nb077AlphaDummy253 F I), (nb077AlphaDummy254 x)),
                            ((nb077AlphaDummy251 F I), (nb077AlphaDummy252 x)),
                            ((nb077AlphaDummy220 F I), (nb077AlphaDummy222 x)),
                            ((nb077AlphaDummy219 F I), (nb077AlphaDummy221 x)),
                            ((nb077AlphaDummy249 F I), (nb077AlphaDummy250 x)),
                            ((nb077AlphaDummy223 F I), (nb077AlphaDummy224 x)),
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
                            ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
                            ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
                            ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                            ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                            ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077AlphaDummy227 F I) ≠ (nb077AlphaDummy231 F I) from
                            (by
                              unfold nb077AlphaDummy231;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0216 F I) 0))))
                          (show (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy232 x) from (by
                              unfold nb077AlphaDummy232;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0217 x) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy227 F I) ≠ (nb077AlphaDummy231 F I) from (by
                                unfold nb077AlphaDummy231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0216 F I) 0))))
                            (show (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy232 x) from (by
                                unfold nb077AlphaDummy232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0217 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb077AlphaDummy231 F I), (nb077AlphaDummy232 x)),
                            ((nb077AlphaDummy227 F I), (nb077AlphaDummy229 x)),
                            ((nb077AlphaDummy228 F I), (nb077AlphaDummy230 x)),
                            ((nb077AlphaDummy253 F I), (nb077AlphaDummy254 x)),
                            ((nb077AlphaDummy251 F I), (nb077AlphaDummy252 x)),
                            ((nb077AlphaDummy220 F I), (nb077AlphaDummy222 x)),
                            ((nb077AlphaDummy219 F I), (nb077AlphaDummy221 x)),
                            ((nb077AlphaDummy249 F I), (nb077AlphaDummy250 x)),
                            ((nb077AlphaDummy223 F I), (nb077AlphaDummy224 x)),
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
                            ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
                            ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
                            ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                            ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                            ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb077AlphaDummy220 F I) ≠ (nb077AlphaDummy227 F I) from (by
                        unfold nb077AlphaDummy227;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0214 F I) 0))))
                    (show (nb077AlphaDummy222 x) ≠ (nb077AlphaDummy229 x) from (by
                        unfold nb077AlphaDummy229;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0215 x) 0)))) (TAlphaVar.there
                      (show (nb077AlphaDummy220 F I) ≠ (nb077AlphaDummy228 F I) from (by
                          unfold nb077AlphaDummy228;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0214 F I) 1))))
                      (show (nb077AlphaDummy222 x) ≠ (nb077AlphaDummy230 x) from (by
                          unfold nb077AlphaDummy230;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0215 x) 1))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy220 F I) ≠ (nb077AlphaDummy253 F I) from (by
                            unfold nb077AlphaDummy253;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0244 F I) 0))))
                        (show (nb077AlphaDummy222 x) ≠ (nb077AlphaDummy254 x) from (by
                            unfold nb077AlphaDummy254;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0245 x) 0))))
                        (TAlphaVar.there
                          (show (nb077AlphaDummy220 F I) ≠ (nb077AlphaDummy251 F I) from
                            (by
                              unfold nb077AlphaDummy251;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0242 F I) 0))))
                          (show (nb077AlphaDummy222 x) ≠ (nb077AlphaDummy252 x) from (by
                              unfold nb077AlphaDummy252;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0243 x) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb077AlphaDummy220 F I))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb077AlphaDummy222 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb077AlphaDummy227 F I) ≠
        (nb077AlphaDummy234 F I) from (by
                                          unfold nb077AlphaDummy234;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0218 F I) 1)))) (show
                                        (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy237 x)
                                        from (by
                                          unfold nb077AlphaDummy237;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0219 x) 1))))
                                      (TAlphaVar.there (show (nb077AlphaDummy227 F I) ≠
        (nb077AlphaDummy233 F I) from (by
          unfold nb077AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0218 F I) 0)))) (show (nb077AlphaDummy229 x) ≠
        (nb077AlphaDummy236 x) from (by
          unfold nb077AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0219 x) 0)))) (TAlphaVar.there (show
        (nb077AlphaDummy227 F I) ≠ (nb077AlphaDummy231 F I) from (by
          unfold nb077AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0216 F I) 0)))) (show (nb077AlphaDummy229 x) ≠
        (nb077AlphaDummy232 x) from (by
          unfold nb077AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0217 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb077AlphaDummy235 F I),
        (nb077AlphaDummy238 x)), ((nb077AlphaDummy234 F I), (nb077AlphaDummy237 x)),
        ((nb077AlphaDummy233 F I), (nb077AlphaDummy236 x)), ((nb077AlphaDummy231 F I),
        (nb077AlphaDummy232 x)), ((nb077AlphaDummy227 F I), (nb077AlphaDummy229 x)),
        ((nb077AlphaDummy228 F I), (nb077AlphaDummy230 x)), ((nb077AlphaDummy253 F I),
        (nb077AlphaDummy254 x)), ((nb077AlphaDummy251 F I), (nb077AlphaDummy252 x)),
        ((nb077AlphaDummy220 F I), (nb077AlphaDummy222 x)), ((nb077AlphaDummy219 F I),
        (nb077AlphaDummy221 x)), ((nb077AlphaDummy249 F I), (nb077AlphaDummy250 x)),
        ((nb077AlphaDummy223 F I), (nb077AlphaDummy224 x)), ((nb077AlphaDummy141 F I),
        (nb077AlphaDummy144 x)), ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
        ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I),
        (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
        (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy234 F
        I) ≠ (nb077AlphaDummy241 F I) from (by
          unfold
            nb077AlphaDummy241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0222
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy242 x) from (by
          unfold
            nb077AlphaDummy242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0223
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠
        (nb077AlphaDummy239 F I) from (by
          unfold
            nb077AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0220
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy240 x) from (by
          unfold
            nb077AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0221
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy227
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠ (nb077AlphaDummy241 F I) from
        (by
          unfold
            nb077AlphaDummy241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0226
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy242 x) from (by
          unfold
            nb077AlphaDummy242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0227
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠
        (nb077AlphaDummy239 F I) from (by
          unfold
            nb077AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0224
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy240 x) from (by
          unfold
            nb077AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0225
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠ (nb077AlphaDummy241 F I) from
        (by
          unfold
            nb077AlphaDummy241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0222
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy242 x) from (by
          unfold
            nb077AlphaDummy242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0223
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠
        (nb077AlphaDummy239 F I) from (by
          unfold
            nb077AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0220
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy240 x) from (by
          unfold
            nb077AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0221
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy227
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠ (nb077AlphaDummy241 F I) from
        (by
          unfold
            nb077AlphaDummy241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0226
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy242 x) from (by
          unfold
            nb077AlphaDummy242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0227
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠
        (nb077AlphaDummy239 F I) from (by
          unfold
            nb077AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0224
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy240 x) from (by
          unfold
            nb077AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0225
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy235 F I), (nb077AlphaDummy238 x)), ((nb077AlphaDummy234 F I),
        (nb077AlphaDummy237 x)), ((nb077AlphaDummy233 F I), (nb077AlphaDummy236 x)),
        ((nb077AlphaDummy231 F I), (nb077AlphaDummy232 x)), ((nb077AlphaDummy227 F I),
        (nb077AlphaDummy229 x)), ((nb077AlphaDummy228 F I), (nb077AlphaDummy230 x)),
        ((nb077AlphaDummy253 F I), (nb077AlphaDummy254 x)), ((nb077AlphaDummy251 F I),
        (nb077AlphaDummy252 x)), ((nb077AlphaDummy220 F I), (nb077AlphaDummy222 x)),
        ((nb077AlphaDummy219 F I), (nb077AlphaDummy221 x)), ((nb077AlphaDummy249 F I),
        (nb077AlphaDummy250 x)), ((nb077AlphaDummy223 F I), (nb077AlphaDummy224 x)),
        ((nb077AlphaDummy141 F I), (nb077AlphaDummy144 x)), ((nb077AlphaDummy140 F I),
        (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
        ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I),
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
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy227 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy227 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy234 F
        I) ≠ (nb077AlphaDummy245 F I) from (by
          unfold
            nb077AlphaDummy245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0230
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy246 x) from (by
          unfold
            nb077AlphaDummy246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0231
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠
        (nb077AlphaDummy243 F I) from (by
          unfold
            nb077AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0228
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy244 x) from (by
          unfold
            nb077AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0229
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy227
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠ (nb077AlphaDummy245 F I) from
        (by
          unfold
            nb077AlphaDummy245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0230
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy246 x) from (by
          unfold
            nb077AlphaDummy246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0231
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy234 F I) ≠
        (nb077AlphaDummy243 F I) from (by
          unfold
            nb077AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0228
                    F I)
                  0)))) (show (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy244 x) from (by
          unfold
            nb077AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0229
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy227
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy235 F
        I) ≠ (nb077AlphaDummy247 F I) from (by
          unfold
            nb077AlphaDummy247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0234
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy248 x) from (by
          unfold
            nb077AlphaDummy248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0235
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠
        (nb077AlphaDummy243 F I) from (by
          unfold
            nb077AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0232
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy244 x) from (by
          unfold
            nb077AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0233
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy235 F
        I) ≠ (nb077AlphaDummy247 F I) from (by
          unfold
            nb077AlphaDummy247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0234
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy248 x) from (by
          unfold
            nb077AlphaDummy248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0235
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy235 F I) ≠
        (nb077AlphaDummy243 F I) from (by
          unfold
            nb077AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0232
                    F I)
                  0)))) (show (nb077AlphaDummy238 x) ≠ (nb077AlphaDummy244 x) from (by
          unfold
            nb077AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0233
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077AlphaDummy227 F I) ≠ (nb077AlphaDummy231 F I) from
                                (by
                                  unfold nb077AlphaDummy231;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0216 F I)
                                          0))))
                              (show (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy232 x) from
                                (by
                                  unfold nb077AlphaDummy232;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0217 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb077AlphaDummy231 F I), (nb077AlphaDummy232 x)),
                              ((nb077AlphaDummy227 F I), (nb077AlphaDummy229 x)),
                              ((nb077AlphaDummy228 F I), (nb077AlphaDummy230 x)),
                              ((nb077AlphaDummy253 F I), (nb077AlphaDummy254 x)),
                              ((nb077AlphaDummy251 F I), (nb077AlphaDummy252 x)),
                              ((nb077AlphaDummy220 F I), (nb077AlphaDummy222 x)),
                              ((nb077AlphaDummy219 F I), (nb077AlphaDummy221 x)),
                              ((nb077AlphaDummy249 F I), (nb077AlphaDummy250 x)),
                              ((nb077AlphaDummy223 F I), (nb077AlphaDummy224 x)),
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
                              ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
                              ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
                              ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                              ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                              ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy227 F I) ≠ (nb077AlphaDummy231 F I) from (by
                                unfold nb077AlphaDummy231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0216 F I) 0))))
                            (show (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy232 x) from (by
                                unfold nb077AlphaDummy232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0217 x) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077AlphaDummy227 F I) ≠ (nb077AlphaDummy231 F I) from
                                (by
                                  unfold nb077AlphaDummy231;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0216 F I)
                                          0))))
                              (show (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy232 x) from
                                (by
                                  unfold nb077AlphaDummy232;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0217 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb077AlphaDummy231 F I), (nb077AlphaDummy232 x)),
                              ((nb077AlphaDummy227 F I), (nb077AlphaDummy229 x)),
                              ((nb077AlphaDummy228 F I), (nb077AlphaDummy230 x)),
                              ((nb077AlphaDummy253 F I), (nb077AlphaDummy254 x)),
                              ((nb077AlphaDummy251 F I), (nb077AlphaDummy252 x)),
                              ((nb077AlphaDummy220 F I), (nb077AlphaDummy222 x)),
                              ((nb077AlphaDummy219 F I), (nb077AlphaDummy221 x)),
                              ((nb077AlphaDummy249 F I), (nb077AlphaDummy250 x)),
                              ((nb077AlphaDummy223 F I), (nb077AlphaDummy224 x)),
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
                              ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
                              ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
                              ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                              ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                              ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
