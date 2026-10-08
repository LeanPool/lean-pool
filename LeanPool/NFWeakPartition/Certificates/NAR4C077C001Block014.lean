/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C077C001Block013

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C077C001Part040`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb077_split_alpha_0026`. -/
@[expose]
noncomputable def nb077SplitAlpha0026 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077AlphaDummy189 F I), (nb077AlphaDummy190 x)),
        ((nb077AlphaDummy187 F I), (nb077AlphaDummy188 x)),
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
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy189 F I))
          (Class.cab (nb077AlphaDummy183 F I)
            (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy139 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                (synCphi (Class.cv (nb077AlphaDummy184 F I))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy189 F I))
            (Class.cab (nb077AlphaDummy183 F I)
              (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy139 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                  (synCphi (Class.cv (nb077AlphaDummy184 F I)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy190 x))
          (Class.cab (nb077AlphaDummy185 x)
            (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy142 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                (synCphi (Class.cv (nb077AlphaDummy186 x))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy190 x))
            (Class.cab (nb077AlphaDummy185 x)
              (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy142 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                  (synCphi (Class.cv (nb077AlphaDummy186 x))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy184 F I) from (by
                      unfold nb077AlphaDummy184;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0170 F I) 1))))
                  (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy186 x) from (by
                      unfold nb077AlphaDummy186;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0172 x) 1))))
                  (TAlphaVar.there
                    (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy183 F I) from (by
                        unfold nb077AlphaDummy183;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0170 F I) 0))))
                    (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy185 x) from (by
                        unfold nb077AlphaDummy185;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0172 x) 0)))) (TAlphaVar.there
                      (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy189 F I) from (by
                          unfold nb077AlphaDummy189;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0174 F I) 0))))
                      (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy190 x) from (by
                          unfold nb077AlphaDummy190;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0175 x) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy187 F I) from (by
                            unfold nb077AlphaDummy187;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0171 F I) 0))))
                        (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy188 x) from (by
                            unfold nb077AlphaDummy188;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0173 x) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((synCmpt (nb077AlphaDummy000 F I) (synCvv)
                                  (synCplc (Class.cv (nb077AlphaDummy000 F I))
                                    (synC1c)))).fv ∪ ((synC1st)).fv) (by decide))
                          (freshVar_injective (((synCmpt x (synCvv)
                                  (synCplc (Class.cv x) (synC1c)))).fv ∪ ((synC1st)).fv)
                            (by decide)) (TAlphaVar.there (freshVar_injective
                              (((synCmpt (nb077AlphaDummy000 F I) (synCvv)
                                    (synCplc (Class.cv (nb077AlphaDummy000 F I))
                                      (synC1c)))).fv ∪ ((synC1st)).fv) (by decide))
                            (freshVar_injective (((synCmpt x (synCvv)
                                    (synCplc (Class.cv x) (synC1c)))).fv ∪ ((synC1st)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
                      ((Class.cv (nb077AlphaDummy141 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077AlphaDummy142 x))).fv ∪
                      ((Class.cv (nb077AlphaDummy144 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077AlphaDummy184 F I) ≠ (nb077AlphaDummy191 F I) from
                            (by
                              unfold nb077AlphaDummy191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0176 F I) 0))))
                          (show (nb077AlphaDummy186 x) ≠ (nb077AlphaDummy193 x) from (by
                              unfold nb077AlphaDummy193;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0177 x) 0))))
                          (TAlphaVar.there (show
                              (nb077AlphaDummy184 F I) ≠ (nb077AlphaDummy192 F I) from (by
                                unfold nb077AlphaDummy192;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0176 F I) 1))))
                            (show (nb077AlphaDummy186 x) ≠ (nb077AlphaDummy194 x) from (by
                                unfold nb077AlphaDummy194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0177 x) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb077AlphaDummy184 F I))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb077AlphaDummy186 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy191 F I) ≠ (nb077AlphaDummy198 F I) from
        (by
          unfold nb077AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0180 F I) 1)))) (show (nb077AlphaDummy193 x) ≠
        (nb077AlphaDummy201 x) from (by
          unfold nb077AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0181 x) 1)))) (TAlphaVar.there (show
        (nb077AlphaDummy191 F I) ≠ (nb077AlphaDummy197 F I) from (by
          unfold nb077AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0180 F I)
                  0)))) (show (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy200 x) from (by
          unfold nb077AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0181 x) 0)))) (TAlphaVar.there (show
        (nb077AlphaDummy191 F I) ≠ (nb077AlphaDummy195 F I) from (by
          unfold nb077AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0178 F I)
                  0)))) (show (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy196 x) from (by
          unfold nb077AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0179 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy199 F I), (nb077AlphaDummy202 x)), ((nb077AlphaDummy198 F I),
        (nb077AlphaDummy201 x)), ((nb077AlphaDummy197 F I), (nb077AlphaDummy200 x)),
        ((nb077AlphaDummy195 F I), (nb077AlphaDummy196 x)), ((nb077AlphaDummy191 F I),
        (nb077AlphaDummy193 x)), ((nb077AlphaDummy192 F I), (nb077AlphaDummy194 x)),
        ((nb077AlphaDummy184 F I), (nb077AlphaDummy186 x)), ((nb077AlphaDummy183 F I),
        (nb077AlphaDummy185 x)), ((nb077AlphaDummy189 F I), (nb077AlphaDummy190 x)),
        ((nb077AlphaDummy187 F I), (nb077AlphaDummy188 x)), ((nb077AlphaDummy141 F I),
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
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠ (nb077AlphaDummy205 F I) from
        (by
          unfold
            nb077AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0184
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy206 x) from (by
          unfold
            nb077AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0185
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠
        (nb077AlphaDummy203 F I) from (by
          unfold
            nb077AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0182
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy204 x) from (by
          unfold
            nb077AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0183
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy191
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠ (nb077AlphaDummy205 F I) from
        (by
          unfold
            nb077AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0188
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy206 x) from (by
          unfold
            nb077AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0189
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠
        (nb077AlphaDummy203 F I) from (by
          unfold
            nb077AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0186
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy204 x) from (by
          unfold
            nb077AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0187
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠ (nb077AlphaDummy205 F I) from
        (by
          unfold
            nb077AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0184
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy206 x) from (by
          unfold
            nb077AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0185
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠
        (nb077AlphaDummy203 F I) from (by
          unfold
            nb077AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0182
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy204 x) from (by
          unfold
            nb077AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0183
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy191
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠ (nb077AlphaDummy205 F I) from
        (by
          unfold
            nb077AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0188
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy206 x) from (by
          unfold
            nb077AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0189
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠
        (nb077AlphaDummy203 F I) from (by
          unfold
            nb077AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0186
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy204 x) from (by
          unfold
            nb077AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0187
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy199 F I), (nb077AlphaDummy202 x)), ((nb077AlphaDummy198 F I),
        (nb077AlphaDummy201 x)), ((nb077AlphaDummy197 F I), (nb077AlphaDummy200 x)),
        ((nb077AlphaDummy195 F I), (nb077AlphaDummy196 x)), ((nb077AlphaDummy191 F I),
        (nb077AlphaDummy193 x)), ((nb077AlphaDummy192 F I), (nb077AlphaDummy194 x)),
        ((nb077AlphaDummy184 F I), (nb077AlphaDummy186 x)), ((nb077AlphaDummy183 F I),
        (nb077AlphaDummy185 x)), ((nb077AlphaDummy189 F I), (nb077AlphaDummy190 x)),
        ((nb077AlphaDummy187 F I), (nb077AlphaDummy188 x)), ((nb077AlphaDummy141 F I),
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
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy191 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb077AlphaDummy191 F I))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb077AlphaDummy193 x))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy198
        F I) ≠ (nb077AlphaDummy209 F I) from (by
          unfold
            nb077AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0192
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy210 x) from (by
          unfold
            nb077AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0193
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠
        (nb077AlphaDummy207 F I) from (by
          unfold
            nb077AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0190
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy208 x) from (by
          unfold
            nb077AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0191
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy191
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠ (nb077AlphaDummy209 F I) from
        (by
          unfold
            nb077AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0192
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy210 x) from (by
          unfold
            nb077AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0193
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠
        (nb077AlphaDummy207 F I) from (by
          unfold
            nb077AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0190
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy208 x) from (by
          unfold
            nb077AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0191
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy191
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy199
        F I) ≠ (nb077AlphaDummy211 F I) from (by
          unfold
            nb077AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0196
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy212 x) from (by
          unfold
            nb077AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0197
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠
        (nb077AlphaDummy207 F I) from (by
          unfold
            nb077AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0194
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy208 x) from (by
          unfold
            nb077AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0195
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy199
        F I) ≠ (nb077AlphaDummy211 F I) from (by
          unfold
            nb077AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0196
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy212 x) from (by
          unfold
            nb077AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0197
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠
        (nb077AlphaDummy207 F I) from (by
          unfold
            nb077AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0194
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy208 x) from (by
          unfold
            nb077AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0195
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy191 F I) ≠ (nb077AlphaDummy195 F I)
                                      from (by
                                        unfold nb077AlphaDummy195;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0178 F I) 0)))) (show
                                      (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy196 x) from
                                      (by
                                        unfold nb077AlphaDummy196;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0179 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed [((nb077AlphaDummy195 F I),
                                      (nb077AlphaDummy196 x)), ((nb077AlphaDummy191 F I),
                                      (nb077AlphaDummy193 x)), ((nb077AlphaDummy192 F I),
                                      (nb077AlphaDummy194 x)), ((nb077AlphaDummy184 F I),
                                      (nb077AlphaDummy186 x)), ((nb077AlphaDummy183 F I),
                                      (nb077AlphaDummy185 x)), ((nb077AlphaDummy189 F I),
                                      (nb077AlphaDummy190 x)), ((nb077AlphaDummy187 F I),
                                      (nb077AlphaDummy188 x)), ((nb077AlphaDummy141 F I),
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
                                    ((nb077AlphaDummy001 F I),
                                      (nb077AlphaDummy002 x F I)),
                                    ((nb077AlphaDummy004 F I),
                                      (nb077AlphaDummy006 x F I)),
                                    ((nb077AlphaDummy003 F I),
                                      (nb077AlphaDummy005 x F I))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb077AlphaDummy191 F I) ≠ (nb077AlphaDummy195 F I)
                                    from (by
                                      unfold nb077AlphaDummy195;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0178 F I)
                                              0)))) (show
                                    (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy196 x) from
                                    (by
                                      unfold nb077AlphaDummy196;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0179 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy191 F I) ≠ (nb077AlphaDummy195 F I)
                                      from (by
                                        unfold nb077AlphaDummy195;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0178 F I) 0)))) (show
                                      (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy196 x) from
                                      (by
                                        unfold nb077AlphaDummy196;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0179 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed [((nb077AlphaDummy195 F I),
                                      (nb077AlphaDummy196 x)), ((nb077AlphaDummy191 F I),
                                      (nb077AlphaDummy193 x)), ((nb077AlphaDummy192 F I),
                                      (nb077AlphaDummy194 x)), ((nb077AlphaDummy184 F I),
                                      (nb077AlphaDummy186 x)), ((nb077AlphaDummy183 F I),
                                      (nb077AlphaDummy185 x)), ((nb077AlphaDummy189 F I),
                                      (nb077AlphaDummy190 x)), ((nb077AlphaDummy187 F I),
                                      (nb077AlphaDummy188 x)), ((nb077AlphaDummy141 F I),
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
                    (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy184 F I) from (by
                        unfold nb077AlphaDummy184;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0170 F I) 1))))
                    (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy186 x) from (by
                        unfold nb077AlphaDummy186;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0172 x) 1)))) (TAlphaVar.there
                      (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy183 F I) from (by
                          unfold nb077AlphaDummy183;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0170 F I) 0))))
                      (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy185 x) from (by
                          unfold nb077AlphaDummy185;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0172 x) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy189 F I) from (by
                            unfold nb077AlphaDummy189;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0174 F I) 0))))
                        (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy190 x) from (by
                            unfold nb077AlphaDummy190;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0175 x) 0))))
                        (TAlphaVar.there
                          (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy187 F I) from
                            (by
                              unfold nb077AlphaDummy187;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0171 F I) 0))))
                          (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy188 x) from (by
                              unfold nb077AlphaDummy188;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0173 x) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((synCmpt (nb077AlphaDummy000 F I) (synCvv)
                                    (synCplc (Class.cv (nb077AlphaDummy000 F I))
                                      (synC1c)))).fv ∪ ((synC1st)).fv) (by decide))
                            (freshVar_injective (((synCmpt x (synCvv)
                                    (synCplc (Class.cv x) (synC1c)))).fv ∪ ((synC1st)).fv)
                              (by decide)) (TAlphaVar.there (freshVar_injective
                                (((synCmpt (nb077AlphaDummy000 F I) (synCvv)
                                      (synCplc (Class.cv (nb077AlphaDummy000 F I))
                                        (synC1c)))).fv ∪ ((synC1st)).fv) (by decide))
                              (freshVar_injective (((synCmpt x (synCvv)
                                      (synCplc (Class.cv x) (synC1c)))).fv ∪ ((synC1st)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
                        ((Class.cv (nb077AlphaDummy141 F I))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb077AlphaDummy142 x))).fv ∪
                        ((Class.cv (nb077AlphaDummy144 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy184 F I) ≠ (nb077AlphaDummy191 F I) from (by
                                unfold nb077AlphaDummy191;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0176 F I) 0))))
                            (show (nb077AlphaDummy186 x) ≠ (nb077AlphaDummy193 x) from (by
                                unfold nb077AlphaDummy193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0177 x) 0))))
                            (TAlphaVar.there (show
                                (nb077AlphaDummy184 F I) ≠ (nb077AlphaDummy192 F I) from
                                (by
                                  unfold nb077AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0176 F I)
                                          1))))
                              (show (nb077AlphaDummy186 x) ≠ (nb077AlphaDummy194 x) from
                                (by
                                  unfold nb077AlphaDummy194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0177 x) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb077AlphaDummy184 F I))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb077AlphaDummy186 x))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy191 F I) ≠ (nb077AlphaDummy198 F I) from (by
          unfold nb077AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0180 F I)
                  1)))) (show (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy201 x) from (by
          unfold nb077AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0181 x) 1)))) (TAlphaVar.there (show
        (nb077AlphaDummy191 F I) ≠ (nb077AlphaDummy197 F I) from (by
          unfold nb077AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0180 F I)
                  0)))) (show (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy200 x) from (by
          unfold nb077AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0181 x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy191 F I) ≠
        (nb077AlphaDummy195 F I) from (by
          unfold nb077AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0178 F I)
                  0)))) (show (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy196 x) from (by
          unfold nb077AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0179 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy199 F I), (nb077AlphaDummy202 x)), ((nb077AlphaDummy198 F I),
        (nb077AlphaDummy201 x)), ((nb077AlphaDummy197 F I), (nb077AlphaDummy200 x)),
        ((nb077AlphaDummy195 F I), (nb077AlphaDummy196 x)), ((nb077AlphaDummy191 F I),
        (nb077AlphaDummy193 x)), ((nb077AlphaDummy192 F I), (nb077AlphaDummy194 x)),
        ((nb077AlphaDummy184 F I), (nb077AlphaDummy186 x)), ((nb077AlphaDummy183 F I),
        (nb077AlphaDummy185 x)), ((nb077AlphaDummy189 F I), (nb077AlphaDummy190 x)),
        ((nb077AlphaDummy187 F I), (nb077AlphaDummy188 x)), ((nb077AlphaDummy141 F I),
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
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠ (nb077AlphaDummy205 F I) from
        (by
          unfold
            nb077AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0184
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy206 x) from (by
          unfold
            nb077AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0185
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠
        (nb077AlphaDummy203 F I) from (by
          unfold
            nb077AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0182
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy204 x) from (by
          unfold
            nb077AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0183
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy191
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠ (nb077AlphaDummy205 F I) from
        (by
          unfold
            nb077AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0188
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy206 x) from (by
          unfold
            nb077AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0189
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠
        (nb077AlphaDummy203 F I) from (by
          unfold
            nb077AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0186
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy204 x) from (by
          unfold
            nb077AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0187
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠ (nb077AlphaDummy205 F I) from
        (by
          unfold
            nb077AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0184
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy206 x) from (by
          unfold
            nb077AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0185
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠
        (nb077AlphaDummy203 F I) from (by
          unfold
            nb077AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0182
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy204 x) from (by
          unfold
            nb077AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0183
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy191
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠ (nb077AlphaDummy205 F I) from
        (by
          unfold
            nb077AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0188
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy206 x) from (by
          unfold
            nb077AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0189
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠
        (nb077AlphaDummy203 F I) from (by
          unfold
            nb077AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0186
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy204 x) from (by
          unfold
            nb077AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0187
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy199 F I), (nb077AlphaDummy202 x)), ((nb077AlphaDummy198 F I),
        (nb077AlphaDummy201 x)), ((nb077AlphaDummy197 F I), (nb077AlphaDummy200 x)),
        ((nb077AlphaDummy195 F I), (nb077AlphaDummy196 x)), ((nb077AlphaDummy191 F I),
        (nb077AlphaDummy193 x)), ((nb077AlphaDummy192 F I), (nb077AlphaDummy194 x)),
        ((nb077AlphaDummy184 F I), (nb077AlphaDummy186 x)), ((nb077AlphaDummy183 F I),
        (nb077AlphaDummy185 x)), ((nb077AlphaDummy189 F I), (nb077AlphaDummy190 x)),
        ((nb077AlphaDummy187 F I), (nb077AlphaDummy188 x)), ((nb077AlphaDummy141 F I),
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
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy191 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077AlphaDummy193
        x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy191 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy198
        F I) ≠ (nb077AlphaDummy209 F I) from (by
          unfold
            nb077AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0192
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy210 x) from (by
          unfold
            nb077AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0193
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠
        (nb077AlphaDummy207 F I) from (by
          unfold
            nb077AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0190
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy208 x) from (by
          unfold
            nb077AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0191
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy191
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠ (nb077AlphaDummy209 F I) from
        (by
          unfold
            nb077AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0192
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy210 x) from (by
          unfold
            nb077AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0193
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠
        (nb077AlphaDummy207 F I) from (by
          unfold
            nb077AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0190
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy208 x) from (by
          unfold
            nb077AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0191
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy191
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy199
        F I) ≠ (nb077AlphaDummy211 F I) from (by
          unfold
            nb077AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0196
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy212 x) from (by
          unfold
            nb077AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0197
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠
        (nb077AlphaDummy207 F I) from (by
          unfold
            nb077AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0194
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy208 x) from (by
          unfold
            nb077AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0195
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy199
        F I) ≠ (nb077AlphaDummy211 F I) from (by
          unfold
            nb077AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0196
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy212 x) from (by
          unfold
            nb077AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0197
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠
        (nb077AlphaDummy207 F I) from (by
          unfold
            nb077AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0194
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy208 x) from (by
          unfold
            nb077AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0195
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077AlphaDummy191 F I) ≠
        (nb077AlphaDummy195 F I) from (by
                                          unfold nb077AlphaDummy195;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0178 F I) 0)))) (show
                                        (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy196 x)
                                        from (by
                                          unfold nb077AlphaDummy196;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0179 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb077AlphaDummy195 F I), (nb077AlphaDummy196 x)),
                                      ((nb077AlphaDummy191 F I), (nb077AlphaDummy193 x)),
                                      ((nb077AlphaDummy192 F I), (nb077AlphaDummy194 x)),
                                      ((nb077AlphaDummy184 F I), (nb077AlphaDummy186 x)),
                                      ((nb077AlphaDummy183 F I), (nb077AlphaDummy185 x)),
                                      ((nb077AlphaDummy189 F I), (nb077AlphaDummy190 x)),
                                      ((nb077AlphaDummy187 F I), (nb077AlphaDummy188 x)),
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
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy191 F I) ≠ (nb077AlphaDummy195 F I)
                                      from (by
                                        unfold nb077AlphaDummy195;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0178 F I) 0)))) (show
                                      (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy196 x) from
                                      (by
                                        unfold nb077AlphaDummy196;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0179 x)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077AlphaDummy191 F I) ≠
        (nb077AlphaDummy195 F I) from (by
                                          unfold nb077AlphaDummy195;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0178 F I) 0)))) (show
                                        (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy196 x)
                                        from (by
                                          unfold nb077AlphaDummy196;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0179 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb077AlphaDummy195 F I), (nb077AlphaDummy196 x)),
                                      ((nb077AlphaDummy191 F I), (nb077AlphaDummy193 x)),
                                      ((nb077AlphaDummy192 F I), (nb077AlphaDummy194 x)),
                                      ((nb077AlphaDummy184 F I), (nb077AlphaDummy186 x)),
                                      ((nb077AlphaDummy183 F I), (nb077AlphaDummy185 x)),
                                      ((nb077AlphaDummy189 F I), (nb077AlphaDummy190 x)),
                                      ((nb077AlphaDummy187 F I), (nb077AlphaDummy188 x)),
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
                                        (nb077AlphaDummy005 x F I))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part041`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb077_split_alpha_0027`. -/
@[expose]
noncomputable def nb077SplitAlpha0027 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077AlphaDummy217 F I), (nb077AlphaDummy218 x)),
        ((nb077AlphaDummy215 F I), (nb077AlphaDummy216 x)),
        ((nb077AlphaDummy184 F I), (nb077AlphaDummy186 x)),
        ((nb077AlphaDummy183 F I), (nb077AlphaDummy185 x)),
        ((nb077AlphaDummy213 F I), (nb077AlphaDummy214 x)),
        ((nb077AlphaDummy187 F I), (nb077AlphaDummy188 x)),
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
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy217 F I))
          (synCphi (Class.cv (nb077AlphaDummy184 F I)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy217 F I))
            (synCphi (Class.cv (nb077AlphaDummy184 F I))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy218 x))
          (synCphi (Class.cv (nb077AlphaDummy186 x)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy218 x))
            (synCphi (Class.cv (nb077AlphaDummy186 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077AlphaDummy184 F I) ≠ (nb077AlphaDummy191 F I) from (by
                      unfold nb077AlphaDummy191;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0176 F I) 0))))
                  (show (nb077AlphaDummy186 x) ≠ (nb077AlphaDummy193 x) from (by
                      unfold nb077AlphaDummy193;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0177 x) 0))))
                  (TAlphaVar.there
                    (show (nb077AlphaDummy184 F I) ≠ (nb077AlphaDummy192 F I) from (by
                        unfold nb077AlphaDummy192;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0176 F I) 1))))
                    (show (nb077AlphaDummy186 x) ≠ (nb077AlphaDummy194 x) from (by
                        unfold nb077AlphaDummy194;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0177 x) 1)))) (TAlphaVar.there
                      (show (nb077AlphaDummy184 F I) ≠ (nb077AlphaDummy217 F I) from (by
                          unfold nb077AlphaDummy217;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0206 F I) 0))))
                      (show (nb077AlphaDummy186 x) ≠ (nb077AlphaDummy218 x) from (by
                          unfold nb077AlphaDummy218;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0207 x) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy184 F I) ≠ (nb077AlphaDummy215 F I) from (by
                            unfold nb077AlphaDummy215;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0204 F I) 0))))
                        (show (nb077AlphaDummy186 x) ≠ (nb077AlphaDummy216 x) from (by
                            unfold nb077AlphaDummy216;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0205 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb077AlphaDummy184 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077AlphaDummy186 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy191 F I) ≠ (nb077AlphaDummy198 F I)
                                      from (by
                                        unfold nb077AlphaDummy198;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0180 F I) 1)))) (show
                                      (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy201 x) from
                                      (by
                                        unfold nb077AlphaDummy201;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0181 x)
                                                1)))) (TAlphaVar.there (show
                                        (nb077AlphaDummy191 F I) ≠
        (nb077AlphaDummy197 F I) from (by
                                          unfold nb077AlphaDummy197;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0180 F I) 0)))) (show
                                        (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy200 x)
                                        from (by
                                          unfold nb077AlphaDummy200;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0181 x) 0))))
                                      (TAlphaVar.there (show (nb077AlphaDummy191 F I) ≠
        (nb077AlphaDummy195 F I) from (by
          unfold nb077AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0178 F I) 0)))) (show (nb077AlphaDummy193 x) ≠
        (nb077AlphaDummy196 x) from (by
          unfold nb077AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0179 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb077AlphaDummy199 F I),
        (nb077AlphaDummy202 x)), ((nb077AlphaDummy198 F I), (nb077AlphaDummy201 x)),
                                        ((nb077AlphaDummy197 F I),
        (nb077AlphaDummy200 x)), ((nb077AlphaDummy195 F I), (nb077AlphaDummy196 x)),
                                        ((nb077AlphaDummy191 F I),
        (nb077AlphaDummy193 x)), ((nb077AlphaDummy192 F I), (nb077AlphaDummy194 x)),
                                        ((nb077AlphaDummy217 F I),
        (nb077AlphaDummy218 x)), ((nb077AlphaDummy215 F I), (nb077AlphaDummy216 x)),
                                        ((nb077AlphaDummy184 F I),
        (nb077AlphaDummy186 x)), ((nb077AlphaDummy183 F I), (nb077AlphaDummy185 x)),
                                        ((nb077AlphaDummy213 F I),
        (nb077AlphaDummy214 x)), ((nb077AlphaDummy187 F I), (nb077AlphaDummy188 x)),
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
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy001 F I),
        (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy198 F I) ≠ (nb077AlphaDummy205 F I) from (by
          unfold
            nb077AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0184
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy206 x) from (by
          unfold
            nb077AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0185
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠
        (nb077AlphaDummy203 F I) from (by
          unfold
            nb077AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0182
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy204 x) from (by
          unfold
            nb077AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0183
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy191
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠
        (nb077AlphaDummy205 F I) from (by
          unfold
            nb077AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0188
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy206 x) from (by
          unfold
            nb077AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0189
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠
        (nb077AlphaDummy203 F I) from (by
          unfold
            nb077AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0186
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy204 x) from (by
          unfold
            nb077AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0187
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠ (nb077AlphaDummy205 F I) from
        (by
          unfold
            nb077AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0184
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy206 x) from (by
          unfold
            nb077AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0185
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠
        (nb077AlphaDummy203 F I) from (by
          unfold
            nb077AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0182
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy204 x) from (by
          unfold
            nb077AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0183
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy191
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠
        (nb077AlphaDummy205 F I) from (by
          unfold
            nb077AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0188
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy206 x) from (by
          unfold
            nb077AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0189
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠
        (nb077AlphaDummy203 F I) from (by
          unfold
            nb077AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0186
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy204 x) from (by
          unfold
            nb077AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0187
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb077AlphaDummy199 F I),
        (nb077AlphaDummy202 x)), ((nb077AlphaDummy198 F I), (nb077AlphaDummy201 x)),
        ((nb077AlphaDummy197 F I), (nb077AlphaDummy200 x)), ((nb077AlphaDummy195 F I),
        (nb077AlphaDummy196 x)), ((nb077AlphaDummy191 F I), (nb077AlphaDummy193 x)),
        ((nb077AlphaDummy192 F I), (nb077AlphaDummy194 x)), ((nb077AlphaDummy217 F I),
        (nb077AlphaDummy218 x)), ((nb077AlphaDummy215 F I), (nb077AlphaDummy216 x)),
        ((nb077AlphaDummy184 F I), (nb077AlphaDummy186 x)), ((nb077AlphaDummy183 F I),
        (nb077AlphaDummy185 x)), ((nb077AlphaDummy213 F I), (nb077AlphaDummy214 x)),
        ((nb077AlphaDummy187 F I), (nb077AlphaDummy188 x)), ((nb077AlphaDummy141 F I),
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
        (((Class.cv (nb077AlphaDummy191 F I))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy191 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy198 F I) ≠ (nb077AlphaDummy209 F I) from (by
          unfold
            nb077AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0192
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy210 x) from (by
          unfold
            nb077AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0193
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠
        (nb077AlphaDummy207 F I) from (by
          unfold
            nb077AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0190
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy208 x) from (by
          unfold
            nb077AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0191
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy191
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠
        (nb077AlphaDummy209 F I) from (by
          unfold
            nb077AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0192
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy210 x) from (by
          unfold
            nb077AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0193
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠
        (nb077AlphaDummy207 F I) from (by
          unfold
            nb077AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0190
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy208 x) from (by
          unfold
            nb077AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0191
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy191
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy199 F I) ≠ (nb077AlphaDummy211 F I) from (by
          unfold
            nb077AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0196
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy212 x) from (by
          unfold
            nb077AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0197
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠
        (nb077AlphaDummy207 F I) from (by
          unfold
            nb077AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0194
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy208 x) from (by
          unfold
            nb077AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0195
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy199 F I) ≠ (nb077AlphaDummy211 F I) from (by
          unfold
            nb077AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0196
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy212 x) from (by
          unfold
            nb077AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0197
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠
        (nb077AlphaDummy207 F I) from (by
          unfold
            nb077AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0194
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy208 x) from (by
          unfold
            nb077AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0195
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy191 F I) ≠ (nb077AlphaDummy195 F I) from (by
                                unfold nb077AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0178 F I) 0))))
                            (show (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy196 x) from (by
                                unfold nb077AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0179 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb077AlphaDummy195 F I), (nb077AlphaDummy196 x)),
                            ((nb077AlphaDummy191 F I), (nb077AlphaDummy193 x)),
                            ((nb077AlphaDummy192 F I), (nb077AlphaDummy194 x)),
                            ((nb077AlphaDummy217 F I), (nb077AlphaDummy218 x)),
                            ((nb077AlphaDummy215 F I), (nb077AlphaDummy216 x)),
                            ((nb077AlphaDummy184 F I), (nb077AlphaDummy186 x)),
                            ((nb077AlphaDummy183 F I), (nb077AlphaDummy185 x)),
                            ((nb077AlphaDummy213 F I), (nb077AlphaDummy214 x)),
                            ((nb077AlphaDummy187 F I), (nb077AlphaDummy188 x)),
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
                          (show (nb077AlphaDummy191 F I) ≠ (nb077AlphaDummy195 F I) from
                            (by
                              unfold nb077AlphaDummy195;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0178 F I) 0))))
                          (show (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy196 x) from (by
                              unfold nb077AlphaDummy196;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0179 x) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy191 F I) ≠ (nb077AlphaDummy195 F I) from (by
                                unfold nb077AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0178 F I) 0))))
                            (show (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy196 x) from (by
                                unfold nb077AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0179 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb077AlphaDummy195 F I), (nb077AlphaDummy196 x)),
                            ((nb077AlphaDummy191 F I), (nb077AlphaDummy193 x)),
                            ((nb077AlphaDummy192 F I), (nb077AlphaDummy194 x)),
                            ((nb077AlphaDummy217 F I), (nb077AlphaDummy218 x)),
                            ((nb077AlphaDummy215 F I), (nb077AlphaDummy216 x)),
                            ((nb077AlphaDummy184 F I), (nb077AlphaDummy186 x)),
                            ((nb077AlphaDummy183 F I), (nb077AlphaDummy185 x)),
                            ((nb077AlphaDummy213 F I), (nb077AlphaDummy214 x)),
                            ((nb077AlphaDummy187 F I), (nb077AlphaDummy188 x)),
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
                    (show (nb077AlphaDummy184 F I) ≠ (nb077AlphaDummy191 F I) from (by
                        unfold nb077AlphaDummy191;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0176 F I) 0))))
                    (show (nb077AlphaDummy186 x) ≠ (nb077AlphaDummy193 x) from (by
                        unfold nb077AlphaDummy193;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0177 x) 0)))) (TAlphaVar.there
                      (show (nb077AlphaDummy184 F I) ≠ (nb077AlphaDummy192 F I) from (by
                          unfold nb077AlphaDummy192;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0176 F I) 1))))
                      (show (nb077AlphaDummy186 x) ≠ (nb077AlphaDummy194 x) from (by
                          unfold nb077AlphaDummy194;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0177 x) 1))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy184 F I) ≠ (nb077AlphaDummy217 F I) from (by
                            unfold nb077AlphaDummy217;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0206 F I) 0))))
                        (show (nb077AlphaDummy186 x) ≠ (nb077AlphaDummy218 x) from (by
                            unfold nb077AlphaDummy218;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0207 x) 0))))
                        (TAlphaVar.there
                          (show (nb077AlphaDummy184 F I) ≠ (nb077AlphaDummy215 F I) from
                            (by
                              unfold nb077AlphaDummy215;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0204 F I) 0))))
                          (show (nb077AlphaDummy186 x) ≠ (nb077AlphaDummy216 x) from (by
                              unfold nb077AlphaDummy216;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0205 x) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb077AlphaDummy184 F I))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb077AlphaDummy186 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb077AlphaDummy191 F I) ≠
        (nb077AlphaDummy198 F I) from (by
                                          unfold nb077AlphaDummy198;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0180 F I) 1)))) (show
                                        (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy201 x)
                                        from (by
                                          unfold nb077AlphaDummy201;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0181 x) 1))))
                                      (TAlphaVar.there (show (nb077AlphaDummy191 F I) ≠
        (nb077AlphaDummy197 F I) from (by
          unfold nb077AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0180 F I) 0)))) (show (nb077AlphaDummy193 x) ≠
        (nb077AlphaDummy200 x) from (by
          unfold nb077AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0181 x) 0)))) (TAlphaVar.there (show
        (nb077AlphaDummy191 F I) ≠ (nb077AlphaDummy195 F I) from (by
          unfold nb077AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0178 F I) 0)))) (show (nb077AlphaDummy193 x) ≠
        (nb077AlphaDummy196 x) from (by
          unfold nb077AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0179 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb077AlphaDummy199 F I),
        (nb077AlphaDummy202 x)), ((nb077AlphaDummy198 F I), (nb077AlphaDummy201 x)),
        ((nb077AlphaDummy197 F I), (nb077AlphaDummy200 x)), ((nb077AlphaDummy195 F I),
        (nb077AlphaDummy196 x)), ((nb077AlphaDummy191 F I), (nb077AlphaDummy193 x)),
        ((nb077AlphaDummy192 F I), (nb077AlphaDummy194 x)), ((nb077AlphaDummy217 F I),
        (nb077AlphaDummy218 x)), ((nb077AlphaDummy215 F I), (nb077AlphaDummy216 x)),
        ((nb077AlphaDummy184 F I), (nb077AlphaDummy186 x)), ((nb077AlphaDummy183 F I),
        (nb077AlphaDummy185 x)), ((nb077AlphaDummy213 F I), (nb077AlphaDummy214 x)),
        ((nb077AlphaDummy187 F I), (nb077AlphaDummy188 x)), ((nb077AlphaDummy141 F I),
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy198 F
        I) ≠ (nb077AlphaDummy205 F I) from (by
          unfold
            nb077AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0184
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy206 x) from (by
          unfold
            nb077AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0185
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠
        (nb077AlphaDummy203 F I) from (by
          unfold
            nb077AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0182
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy204 x) from (by
          unfold
            nb077AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0183
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy191
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠ (nb077AlphaDummy205 F I) from
        (by
          unfold
            nb077AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0188
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy206 x) from (by
          unfold
            nb077AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0189
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠
        (nb077AlphaDummy203 F I) from (by
          unfold
            nb077AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0186
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy204 x) from (by
          unfold
            nb077AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0187
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠ (nb077AlphaDummy205 F I) from
        (by
          unfold
            nb077AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0184
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy206 x) from (by
          unfold
            nb077AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0185
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠
        (nb077AlphaDummy203 F I) from (by
          unfold
            nb077AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0182
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy204 x) from (by
          unfold
            nb077AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0183
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy191
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠ (nb077AlphaDummy205 F I) from
        (by
          unfold
            nb077AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0188
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy206 x) from (by
          unfold
            nb077AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0189
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠
        (nb077AlphaDummy203 F I) from (by
          unfold
            nb077AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0186
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy204 x) from (by
          unfold
            nb077AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0187
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy199 F I), (nb077AlphaDummy202 x)), ((nb077AlphaDummy198 F I),
        (nb077AlphaDummy201 x)), ((nb077AlphaDummy197 F I), (nb077AlphaDummy200 x)),
        ((nb077AlphaDummy195 F I), (nb077AlphaDummy196 x)), ((nb077AlphaDummy191 F I),
        (nb077AlphaDummy193 x)), ((nb077AlphaDummy192 F I), (nb077AlphaDummy194 x)),
        ((nb077AlphaDummy217 F I), (nb077AlphaDummy218 x)), ((nb077AlphaDummy215 F I),
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
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy191 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy191 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy198 F
        I) ≠ (nb077AlphaDummy209 F I) from (by
          unfold
            nb077AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0192
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy210 x) from (by
          unfold
            nb077AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0193
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠
        (nb077AlphaDummy207 F I) from (by
          unfold
            nb077AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0190
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy208 x) from (by
          unfold
            nb077AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0191
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy191
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠ (nb077AlphaDummy209 F I) from
        (by
          unfold
            nb077AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0192
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy210 x) from (by
          unfold
            nb077AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0193
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy198 F I) ≠
        (nb077AlphaDummy207 F I) from (by
          unfold
            nb077AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0190
                    F I)
                  0)))) (show (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy208 x) from (by
          unfold
            nb077AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0191
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy191
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy199 F
        I) ≠ (nb077AlphaDummy211 F I) from (by
          unfold
            nb077AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0196
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy212 x) from (by
          unfold
            nb077AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0197
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠
        (nb077AlphaDummy207 F I) from (by
          unfold
            nb077AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0194
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy208 x) from (by
          unfold
            nb077AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0195
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy199 F
        I) ≠ (nb077AlphaDummy211 F I) from (by
          unfold
            nb077AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0196
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy212 x) from (by
          unfold
            nb077AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0197
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy199 F I) ≠
        (nb077AlphaDummy207 F I) from (by
          unfold
            nb077AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0194
                    F I)
                  0)))) (show (nb077AlphaDummy202 x) ≠ (nb077AlphaDummy208 x) from (by
          unfold
            nb077AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0195
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077AlphaDummy191 F I) ≠ (nb077AlphaDummy195 F I) from
                                (by
                                  unfold nb077AlphaDummy195;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0178 F I)
                                          0))))
                              (show (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy196 x) from
                                (by
                                  unfold nb077AlphaDummy196;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0179 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb077AlphaDummy195 F I), (nb077AlphaDummy196 x)),
                              ((nb077AlphaDummy191 F I), (nb077AlphaDummy193 x)),
                              ((nb077AlphaDummy192 F I), (nb077AlphaDummy194 x)),
                              ((nb077AlphaDummy217 F I), (nb077AlphaDummy218 x)),
                              ((nb077AlphaDummy215 F I), (nb077AlphaDummy216 x)),
                              ((nb077AlphaDummy184 F I), (nb077AlphaDummy186 x)),
                              ((nb077AlphaDummy183 F I), (nb077AlphaDummy185 x)),
                              ((nb077AlphaDummy213 F I), (nb077AlphaDummy214 x)),
                              ((nb077AlphaDummy187 F I), (nb077AlphaDummy188 x)),
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
                              (nb077AlphaDummy191 F I) ≠ (nb077AlphaDummy195 F I) from (by
                                unfold nb077AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0178 F I) 0))))
                            (show (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy196 x) from (by
                                unfold nb077AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0179 x) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077AlphaDummy191 F I) ≠ (nb077AlphaDummy195 F I) from
                                (by
                                  unfold nb077AlphaDummy195;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0178 F I)
                                          0))))
                              (show (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy196 x) from
                                (by
                                  unfold nb077AlphaDummy196;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0179 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb077AlphaDummy195 F I), (nb077AlphaDummy196 x)),
                              ((nb077AlphaDummy191 F I), (nb077AlphaDummy193 x)),
                              ((nb077AlphaDummy192 F I), (nb077AlphaDummy194 x)),
                              ((nb077AlphaDummy217 F I), (nb077AlphaDummy218 x)),
                              ((nb077AlphaDummy215 F I), (nb077AlphaDummy216 x)),
                              ((nb077AlphaDummy184 F I), (nb077AlphaDummy186 x)),
                              ((nb077AlphaDummy183 F I), (nb077AlphaDummy185 x)),
                              ((nb077AlphaDummy213 F I), (nb077AlphaDummy214 x)),
                              ((nb077AlphaDummy187 F I), (nb077AlphaDummy188 x)),
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

theorem nb077_compact_envfresh_0099 (x : Var) (F : Class) (I : Class) :
    TEnvFresh
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
      ((synC1st)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb077AlphaDummy141 F I) (nb077AlphaDummy144 x)
      (nb077_wpp_notmem_0556 F I) (nb077_wpp_notmem_0557 x)
      (TEnvFresh.consFresh (nb077AlphaDummy140 F I) (nb077AlphaDummy143 x)
        (nb077_wpp_notmem_0558 F I) (nb077_wpp_notmem_0559 x)
        (TEnvFresh.consFresh (nb077AlphaDummy139 F I) (nb077AlphaDummy142 x)
          (nb077_wpp_notmem_0560 F I) (nb077_wpp_notmem_0561 x)
          (TEnvFresh.consFresh (nb077AlphaDummy145 F I) (nb077AlphaDummy146 x)
            (nb077_wpp_notmem_0562 F I) (nb077_wpp_notmem_0563 x)
            (TEnvFresh.consFresh (nb077AlphaDummy061 F I) (nb077AlphaDummy064 x)
              (nb077_wpp_notmem_0564 F I) (nb077_wpp_notmem_0565 x)
              (TEnvFresh.consFresh (nb077AlphaDummy060 F I) (nb077AlphaDummy063 x)
                (nb077_wpp_notmem_0566 F I) (nb077_wpp_notmem_0567 x)
                (TEnvFresh.consFresh (nb077AlphaDummy059 F I) (nb077AlphaDummy062 x)
                  (nb077_wpp_notmem_0568 F I) (nb077_wpp_notmem_0569 x)
                  (TEnvFresh.consFresh (nb077AlphaDummy065 F I)
                    (nb077AlphaDummy066 x) (nb077_wpp_notmem_0570 F I)
                    (nb077_wpp_notmem_0571 x) (TEnvFresh.consFresh (nb077AlphaDummy057 F I)
                      (nb077AlphaDummy058 x F) (nb077_wpp_notmem_0572 F I)
                      (nb077_wpp_notmem_0573 x F)
                      (TEnvFresh.consFresh (nb077AlphaDummy055 F I)
                        (nb077AlphaDummy056 x F) (nb077_wpp_notmem_0574 F I)
                        (nb077_wpp_notmem_0575 x F)
                        (TEnvFresh.consFresh (nb077AlphaDummy016 F I)
                          (nb077AlphaDummy018 x F I) (nb077_wpp_notmem_0576 F I)
                          (nb077_wpp_notmem_0577 x F I)
                          (TEnvFresh.consFresh (nb077AlphaDummy015 F I)
                            (nb077AlphaDummy017 x F I) (nb077_wpp_notmem_0578 F I)
                            (nb077_wpp_notmem_0579 x F I)
                            (TEnvFresh.consFresh (nb077AlphaDummy001 F I)
                              (nb077AlphaDummy002 x F I) (nb077_wpp_notmem_0584 F I)
                              (nb077_wpp_notmem_0585 x F I)
                              (TEnvFresh.consFresh (nb077AlphaDummy004 F I)
                                (nb077AlphaDummy006 x F I) (nb077_wpp_notmem_0586 F I)
                                (nb077_wpp_notmem_0587 x F I)
                                (TEnvFresh.consFresh (nb077AlphaDummy003 F I)
                                  (nb077AlphaDummy005 x F I) (nb077_wpp_notmem_0588 F I)
                                  (nb077_wpp_notmem_0589 x F I)
                                  (TEnvFresh.nil ((synC1st)).fv))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb077_wpp_refl_0099`. -/
@[expose]
noncomputable def nb077WppRefl0099 (x : Var) (F : Class) (I : Class) :
    TReflOn
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
      ((synC1st)).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0099 x F I)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
