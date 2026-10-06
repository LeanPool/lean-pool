/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block033

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part098`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0076`. -/
@[expose]
noncomputable def nb090SplitAlpha0076 (v : Var) (u : Var) (A : Class) (h : Var) :
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
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy181 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
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
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy000 A), h),
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
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part099`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0077`. -/
@[expose]
noncomputable def nb090SplitAlpha0077 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_h_u : h ≠ u) (dv_h_v : h ≠ v) (dv_u_v : u ≠ v) :
    TAlphaWff
      [((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (synWf (Class.cv (nb090AlphaDummy000 A))
          (synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))
          (synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A))))
        (Wff.neg (synWfun (synCcnv (Class.cv (nb090AlphaDummy000 A))))))
      (Wff.imp (synWf (Class.cv h) (synCfv (synC2nd) (Class.cv u))
          (synCfv (synC2nd) (Class.cv v))) (Wff.neg (synWfun (synCcnv (Class.cv h))))) :=
  (TAlphaWff.imp (TAlphaWff.conj (TAlphaWff.conj (nb090SplitAlpha0022 v u A h)
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.reflOfClosed
                    [((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
                      ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
                      ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                      ((nb090AlphaDummy001 A), u),
                      ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                    (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj (nb090SplitAlpha0023 v u A h)
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex
                                      (TAlphaWff.neg (nb090SplitAlpha0024 v u A h)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb090SplitAlpha0024 v u A h))))))))))))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
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
        (nb090SplitAlpha0025 v u A h))))) (TAlphaWff.classMem
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
        (nb090SplitAlpha0026 v u A h) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb090AlphaDummy167 A),
        (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
        ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)), ((nb090AlphaDummy165 A),
        (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A),
        (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A),
        (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A),
        v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v
        u A h))] (synCcompl (synCsn (synC0c))) (by
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
        (nb090SplitAlpha0026 v u A h) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb090AlphaDummy167 A),
        (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
        ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)), ((nb090AlphaDummy165 A),
        (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A),
        (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A),
        (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A),
        v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v
        u A h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0027 v u A h))))) (TAlphaWff.classMem
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
        (nb090SplitAlpha0028 v u A h) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb090AlphaDummy203 A),
        (nb090AlphaDummy204 h)), ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
        ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)), ((nb090AlphaDummy201 A),
        (nb090AlphaDummy202 h)), ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A),
        (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A),
        (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A),
        v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v
        u A h))] (synCcompl (synCsn (synC0c))) (by
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
        (nb090SplitAlpha0028 v u A h) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb090AlphaDummy203 A),
        (nb090AlphaDummy204 h)), ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
        ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)), ((nb090AlphaDummy201 A),
        (nb090AlphaDummy202 h)), ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A),
        (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A),
        (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A),
        v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v
        u A h))] (synCcompl (synCsn (synC0c))) (by
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
                                        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy244 A)
                                        from (by
                                          unfold nb090AlphaDummy244;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0290 A) 1))))
                                      (show h ≠ (nb090AlphaDummy246 h) from (by
                                          unfold nb090AlphaDummy246;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0291 h) 1))))
                                      (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy243 A) from (by
          unfold nb090AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0290 A) 0)))) (show h ≠ (nb090AlphaDummy245 h) from (by
          unfold nb090AlphaDummy245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0291 h) 0)))) (TAlphaVar.here _ _ _))))))))))))))))
          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                    (freshVar_injective (((Class.cab (nb090AlphaDummy285 A) (Wff.classEq
                            (Class.cab (nb090AlphaDummy283 A)
                              (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC2nd)
                                (Class.cv (nb090AlphaDummy283 A))))
                            (synCsn (Class.cv (nb090AlphaDummy285 A)))))).fv) (by decide))
                    (freshVar_injective (((Class.cab (nb090AlphaDummy286 u) (Wff.classEq
                            (Class.cab (nb090AlphaDummy284 u)
                              (synWbr (Class.cv u) (synC2nd)
                                (Class.cv (nb090AlphaDummy284 u))))
                            (synCsn (Class.cv (nb090AlphaDummy286 u)))))).fv) (by decide))
                    (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.neg
                                        (nb090SplitAlpha0029 v u A h dv_h_u dv_u_v)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠ (nb090AlphaDummy292 A) from (by
          unfold nb090AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  1)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy294 u) from (by
          unfold nb090AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy291 A) from (by
          unfold nb090AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy293 u) from (by
          unfold nb090AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy321 A) from (by
          unfold
            nb090AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0330
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy322 u) from (by
          unfold
            nb090AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0331
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy295 A) from (by
          unfold
            nb090AlphaDummy295;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0327
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy296 u) from (by
          unfold
            nb090AlphaDummy296;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0329
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy001 A))).fv ∪
        ((Class.cv (nb090AlphaDummy283 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy284 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0030 v u A h))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠ (nb090AlphaDummy292 A) from (by
          unfold nb090AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  1)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy294 u) from (by
          unfold nb090AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy291 A) from (by
          unfold nb090AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy293 u) from (by
          unfold nb090AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy321 A) from (by
          unfold
            nb090AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0330
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy322 u) from (by
          unfold
            nb090AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0331
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy295 A) from (by
          unfold
            nb090AlphaDummy295;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0327
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy296 u) from (by
          unfold
            nb090AlphaDummy296;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0329
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy001 A))).fv ∪
        ((Class.cv (nb090AlphaDummy283 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy284 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0030 v u A h)))))))))))))))) (TAlphaClass.reflOfReflOn
                            [((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)),
                              ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)),
                              ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
                              ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synC2nd) (nb090WppRefl0108 v u A h)))) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy285 A) ≠ (nb090AlphaDummy327 A) from
                                (by
                                  unfold nb090AlphaDummy327;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0336 A) 0))))
                              (show (nb090AlphaDummy286 u) ≠ (nb090AlphaDummy328 u) from
                                (by
                                  unfold nb090AlphaDummy328;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0337 u) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))
      (nb090SplitAlpha0037 v u A h dv_h_v)) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                              (TAlphaWff.neg (nb090SplitAlpha0057 v u A h))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfReflOn
                          [((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                            ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCid) (nb090WppRefl0196 v u A h)))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                              (TAlphaWff.neg (nb090SplitAlpha0057 v u A h))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfReflOn
                          [((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                            ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCid) (nb090WppRefl0196 v u A h)))))))))) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there (Ne.symm
                        (show (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy429 A) from (by
                            unfold nb090AlphaDummy429;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0434 A) 0))))) (Ne.symm
                        (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy430 h) from (by
                            unfold nb090AlphaDummy430;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0435 h) 0)))))
                      (TAlphaVar.there (Ne.symm
                          (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy429 A) from (by
                              unfold nb090AlphaDummy429;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0432 A) 0))))) (Ne.symm
                          (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy430 h) from (by
                              unfold nb090AlphaDummy430;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0433 h) 0)))))
                        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb090SplitAlpha0058 v u A h)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy432 A) from (by
          unfold nb090AlphaDummy432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0464 A) 1)))) (show (nb090AlphaDummy427 h) ≠
        (nb090AlphaDummy434 h) from (by
          unfold nb090AlphaDummy434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0466 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy431 A) from (by
          unfold nb090AlphaDummy431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0464 A)
                  0)))) (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy433 h) from (by
          unfold nb090AlphaDummy433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0466 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy424 A) ≠
        (nb090AlphaDummy461 A) from (by
          unfold nb090AlphaDummy461;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0468 A)
                  0)))) (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy462 h) from (by
          unfold nb090AlphaDummy462;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0469 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy424 A) ≠
        (nb090AlphaDummy435 A) from (by
          unfold nb090AlphaDummy435;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0465 A)
                  0)))) (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy436 h) from (by
          unfold nb090AlphaDummy436;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0467 h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy423 A))).fv ∪
        ((Class.cv (nb090AlphaDummy424 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy426 h))).fv ∪ ((Class.cv (nb090AlphaDummy427 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb090SplitAlpha0059 v u A h)))))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy432 A) from (by
          unfold nb090AlphaDummy432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0464 A) 1)))) (show (nb090AlphaDummy427 h) ≠
        (nb090AlphaDummy434 h) from (by
          unfold nb090AlphaDummy434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0466 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy431 A) from (by
          unfold nb090AlphaDummy431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0464 A)
                  0)))) (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy433 h) from (by
          unfold nb090AlphaDummy433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0466 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy424 A) ≠
        (nb090AlphaDummy461 A) from (by
          unfold nb090AlphaDummy461;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0468 A)
                  0)))) (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy462 h) from (by
          unfold nb090AlphaDummy462;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0469 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy424 A) ≠
        (nb090AlphaDummy435 A) from (by
          unfold nb090AlphaDummy435;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0465 A)
                  0)))) (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy436 h) from (by
          unfold nb090AlphaDummy436;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0467 h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy423 A))).fv ∪
        ((Class.cv (nb090AlphaDummy424 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy426 h))).fv ∪ ((Class.cv (nb090AlphaDummy427 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb090SplitAlpha0059 v u A h)))))))))))))))
                (TAlphaWff.ex (TAlphaWff.conj (nb090SplitAlpha0070 v u A h)
                    (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb090SplitAlpha0071 v u A h)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy582 A) from (by
          unfold nb090AlphaDummy582;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0632 A)
                  1)))) (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy584 h) from (by
          unfold nb090AlphaDummy584;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0634 h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy424 A) ≠
        (nb090AlphaDummy581 A) from (by
          unfold nb090AlphaDummy581;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0632 A)
                  0)))) (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy583 h) from (by
          unfold nb090AlphaDummy583;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0634 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy424 A) ≠
        (nb090AlphaDummy611 A) from (by
          unfold nb090AlphaDummy611;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0636
                    A)
                  0)))) (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy612 h) from (by
          unfold nb090AlphaDummy612;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0637
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy424 A) ≠
        (nb090AlphaDummy585 A) from (by
          unfold nb090AlphaDummy585;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0633
                    A)
                  0)))) (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy586 h) from (by
          unfold nb090AlphaDummy586;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0635
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (Class.cv
        (nb090AlphaDummy000 A)))).fv ∪ ((synCcnv (synCcnv (Class.cv (nb090AlphaDummy000
        A))))).fv) (by decide)) (freshVar_injective (((synCcnv (Class.cv h))).fv ∪ ((synCcnv
        (synCcnv (Class.cv h)))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy425 A))).fv ∪ ((Class.cv (nb090AlphaDummy424 A))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy428 h))).fv ∪ ((Class.cv
        (nb090AlphaDummy427 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0072 v u A h)))))))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy582 A) from (by
          unfold nb090AlphaDummy582;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0632 A)
                  1)))) (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy584 h) from (by
          unfold nb090AlphaDummy584;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0634 h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy424 A) ≠
        (nb090AlphaDummy581 A) from (by
          unfold nb090AlphaDummy581;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0632 A)
                  0)))) (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy583 h) from (by
          unfold nb090AlphaDummy583;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0634 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy424 A) ≠
        (nb090AlphaDummy611 A) from (by
          unfold nb090AlphaDummy611;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0636
                    A)
                  0)))) (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy612 h) from (by
          unfold nb090AlphaDummy612;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0637
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy424 A) ≠
        (nb090AlphaDummy585 A) from (by
          unfold nb090AlphaDummy585;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0633
                    A)
                  0)))) (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy586 h) from (by
          unfold nb090AlphaDummy586;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0635
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (Class.cv
        (nb090AlphaDummy000 A)))).fv ∪ ((synCcnv (synCcnv (Class.cv (nb090AlphaDummy000
        A))))).fv) (by decide)) (freshVar_injective (((synCcnv (Class.cv h))).fv ∪ ((synCcnv
        (synCcnv (Class.cv h)))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy425 A))).fv ∪ ((Class.cv (nb090AlphaDummy424 A))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy428 h))).fv ∪ ((Class.cv
        (nb090AlphaDummy427 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0072 v u A h))))))))))))))))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                        (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy133 A)
                                        from (by
                                          unfold nb090AlphaDummy133;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0124 A) 0))))) (Ne.symm
                                      (show (nb090AlphaDummy132 h) ≠
        (nb090AlphaDummy134 h) from (by
                                          unfold nb090AlphaDummy134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0125 h) 0)))))
                                    (TAlphaVar.there (Ne.symm (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy133 A) from (by
          unfold nb090AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0122 A) 0))))) (Ne.symm (show (nb090AlphaDummy131 h) ≠
        (nb090AlphaDummy134 h) from (by
          unfold nb090AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0123 h) 0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0073 v u A h))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy136 A) from (by
          unfold
            nb090AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154
                    A)
                  1)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy138 h) from (by
          unfold
            nb090AlphaDummy138;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0074 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A),
        (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
        ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A),
        (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001
        A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCcompl
        (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy136 A) from (by
          unfold
            nb090AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154
                    A)
                  1)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy138 h) from (by
          unfold
            nb090AlphaDummy138;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0074 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A),
        (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
        ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A),
        (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001
        A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCcompl
        (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0075 v u A h))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy172 A) from (by
          unfold
            nb090AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192
                    A)
                  1)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy174 h) from (by
          unfold
            nb090AlphaDummy174;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0076 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)), ((nb090AlphaDummy172 A),
        (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
        ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)), ((nb090AlphaDummy175 A),
        (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001
        A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCcompl
        (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy172 A) from (by
          unfold
            nb090AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192
                    A)
                  1)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy174 h) from (by
          unfold
            nb090AlphaDummy174;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0076 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)), ((nb090AlphaDummy172 A),
        (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
        ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)), ((nb090AlphaDummy175 A),
        (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001
        A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCcompl
        (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy130 A) from
                                      (by
                                        unfold nb090AlphaDummy130;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0212 A)
                                                1)))) (show h ≠ (nb090AlphaDummy132 h) from
                                      (by
                                        unfold nb090AlphaDummy132;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0213 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy129 A)
                                        from (by
                                          unfold nb090AlphaDummy129;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0212 A) 0))))
                                      (show h ≠ (nb090AlphaDummy131 h) from (by
                                          unfold nb090AlphaDummy131;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0213 h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy133 A) from (by
          unfold nb090AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0210 A) 0)))) (show h ≠ (nb090AlphaDummy134 h) from (by
          unfold nb090AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0211 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy425 A) from (by
          unfold nb090AlphaDummy425;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0596 A) 2)))) (show h ≠ (nb090AlphaDummy428 h) from (by
          unfold nb090AlphaDummy428;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0598 h) 2)))) (TAlphaVar.there (show
        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy424 A) from (by
          unfold nb090AlphaDummy424;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0596 A) 1)))) (show h ≠ (nb090AlphaDummy427 h) from (by
          unfold nb090AlphaDummy427;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0598 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy423 A) from (by
          unfold nb090AlphaDummy423;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0596 A) 0)))) (show h ≠ (nb090AlphaDummy426 h) from (by
          unfold nb090AlphaDummy426;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0598 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy429 A) from (by
          unfold nb090AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0597 A)
                  0)))) (show h ≠ (nb090AlphaDummy430 h) from (by
          unfold nb090AlphaDummy430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0599 h)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
