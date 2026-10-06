/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block026

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part078`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0056`. -/
@[expose]
noncomputable def nb090SplitAlpha0056 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)),
        ((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)),
        ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
        ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
        ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)),
        ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy205 A))
          (synCphi (Class.cv (nb090AlphaDummy172 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy205 A))
            (synCphi (Class.cv (nb090AlphaDummy172 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy206 h))
          (synCphi (Class.cv (nb090AlphaDummy174 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy206 h))
            (synCphi (Class.cv (nb090AlphaDummy174 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy179 A) from (by
                      unfold nb090AlphaDummy179;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0170 A) 0))))
                  (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy181 h) from (by
                      unfold nb090AlphaDummy181;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0171 h) 0))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy180 A) from (by
                        unfold nb090AlphaDummy180;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0170 A) 1))))
                    (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy182 h) from (by
                        unfold nb090AlphaDummy182;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0171 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy205 A) from (by
                          unfold nb090AlphaDummy205;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0200 A) 0))))
                      (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy206 h) from (by
                          unfold nb090AlphaDummy206;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0201 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy203 A) from (by
                            unfold nb090AlphaDummy203;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0198 A) 0))))
                        (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy204 h) from (by
                            unfold nb090AlphaDummy204;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0199 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy172 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy174 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy186 A) from
                                      (by
                                        unfold nb090AlphaDummy186;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0174 A)
                                                1)))) (show (nb090AlphaDummy181 h) ≠
                                        (nb090AlphaDummy189 h) from (by
                                        unfold nb090AlphaDummy189;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0175 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy185 A)
                                        from (by
                                          unfold nb090AlphaDummy185;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0174 A) 0)))) (show
                                        (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy188 h)
                                        from (by
                                          unfold nb090AlphaDummy188;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0175 h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy179 A) ≠
        (nb090AlphaDummy183 A) from (by
          unfold nb090AlphaDummy183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0172 A) 0)))) (show (nb090AlphaDummy181 h) ≠
        (nb090AlphaDummy184 h) from (by
          unfold nb090AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0173 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb090AlphaDummy187 A),
        (nb090AlphaDummy190 h)), ((nb090AlphaDummy186 A), (nb090AlphaDummy189 h)),
                                        ((nb090AlphaDummy185 A), (nb090AlphaDummy188 h)),
                                        ((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)),
                                        ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)),
                                        ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
                                        ((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)),
                                        ((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)),
                                        ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                                        ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                                        ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)),
                                        ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
                                        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                        ((nb090AlphaDummy000 A), h),
                                        ((nb090AlphaDummy002 A), v),
                                        ((nb090AlphaDummy001 A), u),
                                        ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb090AlphaDummy187 A), (nb090AlphaDummy190 h)),
        ((nb090AlphaDummy186 A), (nb090AlphaDummy189 h)), ((nb090AlphaDummy185 A),
        (nb090AlphaDummy188 h)), ((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)),
        ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)), ((nb090AlphaDummy180 A),
        (nb090AlphaDummy182 h)), ((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)),
        ((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)), ((nb090AlphaDummy172 A),
        (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
        ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)), ((nb090AlphaDummy175 A),
        (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A),
        (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy197 A) from (by
          unfold
            nb090AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy198 h) from (by
          unfold
            nb090AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy197 A) from (by
          unfold
            nb090AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy198 h) from (by
          unfold
            nb090AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy187 A) ≠ (nb090AlphaDummy199 A) from (by
          unfold
            nb090AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy200 h) from (by
          unfold
            nb090AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy187 A) ≠ (nb090AlphaDummy199 A) from (by
          unfold
            nb090AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy200 h) from (by
          unfold
            nb090AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from (by
                                unfold nb090AlphaDummy183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                            (show (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from (by
                                unfold nb090AlphaDummy184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)),
                            ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)),
                            ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
                            ((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)),
                            ((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)),
                            ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                            ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                            ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)),
                            ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
                            ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                            ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                            ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                            ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                            ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                            ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                            ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                            ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                            ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from (by
                              unfold nb090AlphaDummy183;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                          (show (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from (by
                              unfold nb090AlphaDummy184;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from (by
                                unfold nb090AlphaDummy183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                            (show (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from (by
                                unfold nb090AlphaDummy184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)),
                            ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)),
                            ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
                            ((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)),
                            ((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)),
                            ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                            ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                            ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)),
                            ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
                            ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                            ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                            ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                            ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                            ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                            ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                            ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                            ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                            ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy179 A) from (by
                        unfold nb090AlphaDummy179;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0170 A) 0))))
                    (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy181 h) from (by
                        unfold nb090AlphaDummy181;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0171 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy180 A) from (by
                          unfold nb090AlphaDummy180;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0170 A) 1))))
                      (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy182 h) from (by
                          unfold nb090AlphaDummy182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0171 h) 1))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy205 A) from (by
                            unfold nb090AlphaDummy205;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0200 A) 0))))
                        (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy206 h) from (by
                            unfold nb090AlphaDummy206;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0201 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy203 A) from (by
                              unfold nb090AlphaDummy203;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0198 A) 0))))
                          (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy204 h) from (by
                              unfold nb090AlphaDummy204;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0199 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090AlphaDummy172 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy174 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090AlphaDummy179 A) ≠
        (nb090AlphaDummy186 A) from (by
                                          unfold nb090AlphaDummy186;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0174 A) 1)))) (show
                                        (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy189 h)
                                        from (by
                                          unfold nb090AlphaDummy189;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0175 h) 1))))
                                      (TAlphaVar.there (show (nb090AlphaDummy179 A) ≠
        (nb090AlphaDummy185 A) from (by
          unfold nb090AlphaDummy185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0174 A) 0)))) (show (nb090AlphaDummy181 h) ≠
        (nb090AlphaDummy188 h) from (by
          unfold nb090AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0175 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from (by
          unfold nb090AlphaDummy183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0172 A) 0)))) (show (nb090AlphaDummy181 h) ≠
        (nb090AlphaDummy184 h) from (by
          unfold nb090AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0173 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy187 A),
        (nb090AlphaDummy190 h)), ((nb090AlphaDummy186 A), (nb090AlphaDummy189 h)),
        ((nb090AlphaDummy185 A), (nb090AlphaDummy188 h)), ((nb090AlphaDummy183 A),
        (nb090AlphaDummy184 h)), ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)),
        ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)), ((nb090AlphaDummy205 A),
        (nb090AlphaDummy206 h)), ((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)),
        ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A),
        (nb090AlphaDummy173 h)), ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)),
        ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠ (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠ (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy187 A), (nb090AlphaDummy190 h)), ((nb090AlphaDummy186 A),
        (nb090AlphaDummy189 h)), ((nb090AlphaDummy185 A), (nb090AlphaDummy188 h)),
        ((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)), ((nb090AlphaDummy179 A),
        (nb090AlphaDummy181 h)), ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
        ((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)), ((nb090AlphaDummy203 A),
        (nb090AlphaDummy204 h)), ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
        ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)), ((nb090AlphaDummy201 A),
        (nb090AlphaDummy202 h)), ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A),
        (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A),
        (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A),
        (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy181 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy197 A) from (by
          unfold
            nb090AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy198 h) from (by
          unfold
            nb090AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy197 A) from (by
          unfold
            nb090AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy198 h) from (by
          unfold
            nb090AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy187 A) ≠ (nb090AlphaDummy199 A) from (by
          unfold
            nb090AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy200 h) from (by
          unfold
            nb090AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy187 A) ≠ (nb090AlphaDummy199 A) from (by
          unfold
            nb090AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy200 h) from (by
          unfold
            nb090AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from
                                (by
                                  unfold nb090AlphaDummy183;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                              (show (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from
                                (by
                                  unfold nb090AlphaDummy184;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)),
                              ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)),
                              ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
                              ((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)),
                              ((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)),
                              ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                              ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                              ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)),
                              ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
                              ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                              ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                              ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                              ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                              ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                              ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                              ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                              ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                              ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from (by
                                unfold nb090AlphaDummy183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                            (show (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from (by
                                unfold nb090AlphaDummy184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from
                                (by
                                  unfold nb090AlphaDummy183;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                              (show (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from
                                (by
                                  unfold nb090AlphaDummy184;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)),
                              ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)),
                              ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
                              ((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)),
                              ((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)),
                              ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                              ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                              ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)),
                              ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
                              ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                              ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                              ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                              ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                              ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                              ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                              ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                              ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                              ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part079`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0057`. -/
@[expose]
noncomputable def nb090SplitAlpha0057 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classEq (Class.cv (nb090AlphaDummy429 A))
          (synCop (Class.cv (nb090AlphaDummy423 A)) (Class.cv (nb090AlphaDummy424 A))))
        (Wff.neg (synWex (nb090AlphaDummy425 A) (synWa
              (synWbr (Class.cv (nb090AlphaDummy423 A))
                (synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))
                (Class.cv (nb090AlphaDummy425 A)))
              (synWbr (Class.cv (nb090AlphaDummy425 A))
                (synCcnv (Class.cv (nb090AlphaDummy000 A)))
                (Class.cv (nb090AlphaDummy424 A)))))))
      (Wff.imp (Wff.classEq (Class.cv (nb090AlphaDummy430 h))
          (synCop (Class.cv (nb090AlphaDummy426 h)) (Class.cv (nb090AlphaDummy427 h))))
        (Wff.neg (synWex (nb090AlphaDummy428 h) (synWa
              (synWbr (Class.cv (nb090AlphaDummy426 h))
                (synCcnv (synCcnv (Class.cv h))) (Class.cv (nb090AlphaDummy428 h)))
              (synWbr (Class.cv (nb090AlphaDummy428 h)) (synCcnv (Class.cv h))
                (Class.cv (nb090AlphaDummy427 h))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy429 A) from (by
                unfold nb090AlphaDummy429;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0434 A) 0)))))
          (Ne.symm (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy430 h) from (by
                unfold nb090AlphaDummy430;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0435 h) 0)))))
          (TAlphaVar.there (Ne.symm
              (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy429 A) from (by
                  unfold nb090AlphaDummy429;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0432 A) 0)))))
            (Ne.symm (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy430 h) from (by
                  unfold nb090AlphaDummy430;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0433 h) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0038 v u A h)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy432 A) from
                                    (by
                                      unfold nb090AlphaDummy432;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0464 A)
                                              1)))) (show
                                    (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy434 h) from
                                    (by
                                      unfold nb090AlphaDummy434;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0466 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy431 A) from
                                      (by
                                        unfold nb090AlphaDummy431;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0464 A)
                                                0)))) (show (nb090AlphaDummy427 h) ≠
                                        (nb090AlphaDummy433 h) from (by
                                        unfold nb090AlphaDummy433;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0466 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy461 A)
                                        from (by
                                          unfold nb090AlphaDummy461;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0468 A) 0)))) (show
                                        (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy462 h)
                                        from (by
                                          unfold nb090AlphaDummy462;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0469 h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy424 A) ≠
        (nb090AlphaDummy435 A) from (by
          unfold nb090AlphaDummy435;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0465 A) 0)))) (show (nb090AlphaDummy427 h) ≠
        (nb090AlphaDummy436 h) from (by
          unfold nb090AlphaDummy436;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0467 h) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb090AlphaDummy423 A))).fv ∪
                                      ((Class.cv (nb090AlphaDummy424 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb090AlphaDummy426 h))).fv ∪
                                      ((Class.cv (nb090AlphaDummy427 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (nb090SplitAlpha0039 v u A h)
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy463 A),
        (nb090AlphaDummy464 h)), ((nb090AlphaDummy432 A), (nb090AlphaDummy434 h)),
        ((nb090AlphaDummy431 A), (nb090AlphaDummy433 h)), ((nb090AlphaDummy461 A),
        (nb090AlphaDummy462 h)), ((nb090AlphaDummy435 A), (nb090AlphaDummy436 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A),
        (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synCcompl (synCsn (synC0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c])))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy432 A) from
                                    (by
                                      unfold nb090AlphaDummy432;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0464 A)
                                              1)))) (show
                                    (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy434 h) from
                                    (by
                                      unfold nb090AlphaDummy434;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0466 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy431 A) from
                                      (by
                                        unfold nb090AlphaDummy431;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0464 A)
                                                0)))) (show (nb090AlphaDummy427 h) ≠
                                        (nb090AlphaDummy433 h) from (by
                                        unfold nb090AlphaDummy433;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0466 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy461 A)
                                        from (by
                                          unfold nb090AlphaDummy461;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0468 A) 0)))) (show
                                        (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy462 h)
                                        from (by
                                          unfold nb090AlphaDummy462;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0469 h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy424 A) ≠
        (nb090AlphaDummy435 A) from (by
          unfold nb090AlphaDummy435;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0465 A) 0)))) (show (nb090AlphaDummy427 h) ≠
        (nb090AlphaDummy436 h) from (by
          unfold nb090AlphaDummy436;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0467 h) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb090AlphaDummy423 A))).fv ∪
                                      ((Class.cv (nb090AlphaDummy424 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb090AlphaDummy426 h))).fv ∪
                                      ((Class.cv (nb090AlphaDummy427 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (nb090SplitAlpha0039 v u A h)
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy463 A),
        (nb090AlphaDummy464 h)), ((nb090AlphaDummy432 A), (nb090AlphaDummy434 h)),
        ((nb090AlphaDummy431 A), (nb090AlphaDummy433 h)), ((nb090AlphaDummy461 A),
        (nb090AlphaDummy462 h)), ((nb090AlphaDummy435 A), (nb090AlphaDummy436 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A),
        (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synCcompl (synCsn (synC0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0040 v u A h)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090AlphaDummy425 A) ≠
        (nb090AlphaDummy468 A) from (by
          unfold nb090AlphaDummy468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0502 A) 1)))) (show (nb090AlphaDummy428 h) ≠
        (nb090AlphaDummy470 h) from (by
          unfold nb090AlphaDummy470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0504 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy467 A) from (by
          unfold nb090AlphaDummy467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0502 A) 0)))) (show (nb090AlphaDummy428 h) ≠
        (nb090AlphaDummy469 h) from (by
          unfold nb090AlphaDummy469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0504 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy497 A) from (by
          unfold nb090AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0506 A) 0)))) (show (nb090AlphaDummy428 h) ≠
        (nb090AlphaDummy498 h) from (by
          unfold nb090AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0507 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy471 A) from (by
          unfold nb090AlphaDummy471;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0503 A) 0)))) (show (nb090AlphaDummy428 h) ≠
        (nb090AlphaDummy472 h) from (by
          unfold nb090AlphaDummy472;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0505 h) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb090AlphaDummy423 A))).fv ∪ ((Class.cv (nb090AlphaDummy425 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy426 h))).fv ∪
        ((Class.cv (nb090AlphaDummy428 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0041 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy499 A), (nb090AlphaDummy500 h)), ((nb090AlphaDummy468 A),
        (nb090AlphaDummy470 h)), ((nb090AlphaDummy467 A), (nb090AlphaDummy469 h)),
        ((nb090AlphaDummy497 A), (nb090AlphaDummy498 h)), ((nb090AlphaDummy471 A),
        (nb090AlphaDummy472 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A),
        (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090AlphaDummy425 A) ≠
        (nb090AlphaDummy468 A) from (by
          unfold nb090AlphaDummy468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0502 A) 1)))) (show (nb090AlphaDummy428 h) ≠
        (nb090AlphaDummy470 h) from (by
          unfold nb090AlphaDummy470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0504 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy467 A) from (by
          unfold nb090AlphaDummy467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0502 A) 0)))) (show (nb090AlphaDummy428 h) ≠
        (nb090AlphaDummy469 h) from (by
          unfold nb090AlphaDummy469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0504 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy497 A) from (by
          unfold nb090AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0506 A) 0)))) (show (nb090AlphaDummy428 h) ≠
        (nb090AlphaDummy498 h) from (by
          unfold nb090AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0507 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy471 A) from (by
          unfold nb090AlphaDummy471;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0503 A) 0)))) (show (nb090AlphaDummy428 h) ≠
        (nb090AlphaDummy472 h) from (by
          unfold nb090AlphaDummy472;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0505 h) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb090AlphaDummy423 A))).fv ∪ ((Class.cv (nb090AlphaDummy425 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy426 h))).fv ∪
        ((Class.cv (nb090AlphaDummy428 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0041 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy499 A), (nb090AlphaDummy500 h)), ((nb090AlphaDummy468 A),
        (nb090AlphaDummy470 h)), ((nb090AlphaDummy467 A), (nb090AlphaDummy469 h)),
        ((nb090AlphaDummy497 A), (nb090AlphaDummy498 h)), ((nb090AlphaDummy471 A),
        (nb090AlphaDummy472 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A),
        (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex
                (TAlphaWff.ex (TAlphaWff.neg (nb090SplitAlpha0050 v u A h))))))
          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0051 v u A h)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090AlphaDummy424 A) ≠
        (nb090AlphaDummy582 A) from (by
          unfold nb090AlphaDummy582;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0632 A) 1)))) (show (nb090AlphaDummy427 h) ≠
        (nb090AlphaDummy584 h) from (by
          unfold nb090AlphaDummy584;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0634 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy581 A) from (by
          unfold nb090AlphaDummy581;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0632 A) 0)))) (show (nb090AlphaDummy427 h) ≠
        (nb090AlphaDummy583 h) from (by
          unfold nb090AlphaDummy583;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0634 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy611 A) from (by
          unfold nb090AlphaDummy611;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0636 A) 0)))) (show (nb090AlphaDummy427 h) ≠
        (nb090AlphaDummy612 h) from (by
          unfold nb090AlphaDummy612;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0637 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy585 A) from (by
          unfold nb090AlphaDummy585;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0633 A) 0)))) (show (nb090AlphaDummy427 h) ≠
        (nb090AlphaDummy586 h) from (by
          unfold nb090AlphaDummy586;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0635 h) 0)))) (TAlphaVar.there (freshVar_injective
        (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪ ((synCcnv (synCcnv (Class.cv
        (nb090AlphaDummy000 A))))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb090AlphaDummy425 A))).fv ∪ ((Class.cv (nb090AlphaDummy424 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy428 h))).fv ∪
        ((Class.cv (nb090AlphaDummy427 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0052 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy613 A), (nb090AlphaDummy614 h)), ((nb090AlphaDummy582 A),
        (nb090AlphaDummy584 h)), ((nb090AlphaDummy581 A), (nb090AlphaDummy583 h)),
        ((nb090AlphaDummy611 A), (nb090AlphaDummy612 h)), ((nb090AlphaDummy585 A),
        (nb090AlphaDummy586 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A),
        (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090AlphaDummy424 A) ≠
        (nb090AlphaDummy582 A) from (by
          unfold nb090AlphaDummy582;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0632 A) 1)))) (show (nb090AlphaDummy427 h) ≠
        (nb090AlphaDummy584 h) from (by
          unfold nb090AlphaDummy584;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0634 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy581 A) from (by
          unfold nb090AlphaDummy581;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0632 A) 0)))) (show (nb090AlphaDummy427 h) ≠
        (nb090AlphaDummy583 h) from (by
          unfold nb090AlphaDummy583;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0634 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy611 A) from (by
          unfold nb090AlphaDummy611;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0636 A) 0)))) (show (nb090AlphaDummy427 h) ≠
        (nb090AlphaDummy612 h) from (by
          unfold nb090AlphaDummy612;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0637 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy585 A) from (by
          unfold nb090AlphaDummy585;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0633 A) 0)))) (show (nb090AlphaDummy427 h) ≠
        (nb090AlphaDummy586 h) from (by
          unfold nb090AlphaDummy586;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0635 h) 0)))) (TAlphaVar.there (freshVar_injective
        (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪ ((synCcnv (synCcnv (Class.cv
        (nb090AlphaDummy000 A))))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb090AlphaDummy425 A))).fv ∪ ((Class.cv (nb090AlphaDummy424 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy428 h))).fv ∪
        ((Class.cv (nb090AlphaDummy427 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0052 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy613 A), (nb090AlphaDummy614 h)), ((nb090AlphaDummy582 A),
        (nb090AlphaDummy584 h)), ((nb090AlphaDummy581 A), (nb090AlphaDummy583 h)),
        ((nb090AlphaDummy611 A), (nb090AlphaDummy612 h)), ((nb090AlphaDummy585 A),
        (nb090AlphaDummy586 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A),
        (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
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
                                  (TAlphaWff.neg (nb090SplitAlpha0053 v u A h)))))
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
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0054 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A),
        (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
        ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A),
        (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A),
        (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
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
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0054 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A),
        (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
        ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A),
        (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A),
        (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb090SplitAlpha0055 v u A h)))))
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
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0056 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)), ((nb090AlphaDummy172 A),
        (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
        ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)), ((nb090AlphaDummy175 A),
        (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A),
        (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
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
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0056 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)), ((nb090AlphaDummy172 A),
        (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
        ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)), ((nb090AlphaDummy175 A),
        (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A),
        (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
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
                                  (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy425 A) from (by
                                    unfold nb090AlphaDummy425;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0596 A)
                                            2)))) (show h ≠ (nb090AlphaDummy428 h) from (by
                                    unfold nb090AlphaDummy428;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0598 h)
                                            2)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy424 A) from
                                    (by
                                      unfold nb090AlphaDummy424;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0596 A)
                                              1)))) (show h ≠ (nb090AlphaDummy427 h) from (by
                                      unfold nb090AlphaDummy427;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0598 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy423 A) from
                                      (by
                                        unfold nb090AlphaDummy423;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0596 A)
                                                0)))) (show h ≠ (nb090AlphaDummy426 h) from
                                      (by
                                        unfold nb090AlphaDummy426;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0598 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy429 A)
                                        from (by
                                          unfold nb090AlphaDummy429;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0597 A) 0))))
                                      (show h ≠ (nb090AlphaDummy430 h) from (by
                                          unfold nb090AlphaDummy430;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0599 h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy421 A) from (by
          unfold nb090AlphaDummy421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0594 A) 0)))) (show h ≠ (nb090AlphaDummy422 h) from (by
          unfold nb090AlphaDummy422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0595 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy419 A) from (by
          unfold nb090AlphaDummy419;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0592 A) 0)))) (show h ≠ (nb090AlphaDummy420 h) from (by
          unfold nb090AlphaDummy420;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0593 h) 0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))

theorem nb090_wpp_notmem_1584 (A : Class) : (nb090AlphaDummy421 A) ∉ ((synCid)).fv :=
  by simpa only [nb090AlphaDummy421, fv_syn_cid] using (nb090_compact_fv_empty_0340 A)

theorem nb090_wpp_notmem_1585 (h : Var) : (nb090AlphaDummy422 h) ∉ ((synCid)).fv := by
  simpa only [nb090AlphaDummy422, fv_syn_cid] using (nb090_compact_fv_empty_0341 h)

theorem nb090_wpp_notmem_1586 (A : Class) : (nb090AlphaDummy419 A) ∉ ((synCid)).fv :=
  by simpa only [nb090AlphaDummy419, fv_syn_cid] using (nb090_compact_fv_empty_0342 A)

theorem nb090_wpp_notmem_1587 (h : Var) : (nb090AlphaDummy420 h) ∉ ((synCid)).fv := by
  simpa only [nb090AlphaDummy420, fv_syn_cid] using (nb090_compact_fv_empty_0343 h)

theorem nb090_compact_envfresh_0196 (v : Var) (u : Var) (A : Class) (h : Var) :
    TEnvFresh
      [((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      ((synCid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb090AlphaDummy421 A) (nb090AlphaDummy422 h)
      (nb090_wpp_notmem_1584 A) (nb090_wpp_notmem_1585 h)
      (TEnvFresh.consFresh (nb090AlphaDummy419 A) (nb090AlphaDummy420 h)
        (nb090_wpp_notmem_1586 A) (nb090_wpp_notmem_1587 h)
        (TEnvFresh.consFresh (nb090AlphaDummy000 A) h (nb090_wpp_notmem_0606 A)
          (nb090_wpp_notmem_0607 h)
          (TEnvFresh.consFresh (nb090AlphaDummy002 A) v (nb090_wpp_notmem_0608 A)
            (nb090_wpp_notmem_0609 v)
            (TEnvFresh.consFresh (nb090AlphaDummy001 A) u (nb090_wpp_notmem_0610 A)
              (nb090_wpp_notmem_0611 u) (TEnvFresh.consFresh (nb090AlphaDummy003 A)
                (nb090AlphaDummy004 v u A h) (nb090_wpp_notmem_0612 A)
                (nb090_wpp_notmem_0613 v u A h) (TEnvFresh.nil ((synCid)).fv)))))))

/-- Checked nominal proof certificate identified upstream as `nb090_wpp_refl_0196`. -/
@[expose]
noncomputable def nb090WppRefl0196 (v : Var) (u : Var) (A : Class) (h : Var) :
    TReflOn
      [((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      ((synCid)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0196 v u A h)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
