/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block008

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part031`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0007`. -/
@[expose]
noncomputable def nb090SplitAlpha0007 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy177 A), (nb090AlphaDummy178 h)),
        ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy177 A))
          (Class.cab (nb090AlphaDummy171 A)
            (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy130 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                (synCphi (Class.cv (nb090AlphaDummy172 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy177 A))
            (Class.cab (nb090AlphaDummy171 A)
              (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy130 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                  (synCphi (Class.cv (nb090AlphaDummy172 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy178 h))
          (Class.cab (nb090AlphaDummy173 h)
            (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy132 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                (synCphi (Class.cv (nb090AlphaDummy174 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy178 h))
            (Class.cab (nb090AlphaDummy173 h)
              (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy132 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                  (synCphi (Class.cv (nb090AlphaDummy174 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy172 A) from (by
                      unfold nb090AlphaDummy172;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0164 A) 1))))
                  (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy174 h) from (by
                      unfold nb090AlphaDummy174;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0166 h) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy171 A) from (by
                        unfold nb090AlphaDummy171;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0164 A) 0))))
                    (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy173 h) from (by
                        unfold nb090AlphaDummy173;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0166 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy177 A) from (by
                          unfold nb090AlphaDummy177;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0168 A) 0))))
                      (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy178 h) from (by
                          unfold nb090AlphaDummy178;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0169 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy175 A) from (by
                            unfold nb090AlphaDummy175;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0165 A) 0))))
                        (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy176 h) from (by
                            unfold nb090AlphaDummy176;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0167 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy130 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy129 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090AlphaDummy132 h))).fv ∪
                      ((Class.cv (nb090AlphaDummy131 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
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
                                    (mem_lt_freshVar (nb090_support_mem_0171 h) 0))))
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
                                      (mem_lt_freshVar (nb090_support_mem_0171 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy172 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy174 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy186 A) from (by
          unfold nb090AlphaDummy186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0174 A) 1)))) (show (nb090AlphaDummy181 h) ≠
        (nb090AlphaDummy189 h) from (by
          unfold nb090AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0175 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy185 A) from (by
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
                  (nb090_support_mem_0172 A)
                  0)))) (show (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from (by
          unfold nb090AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0173 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy187 A), (nb090AlphaDummy190 h)), ((nb090AlphaDummy186 A),
        (nb090AlphaDummy189 h)), ((nb090AlphaDummy185 A), (nb090AlphaDummy188 h)),
        ((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)), ((nb090AlphaDummy179 A),
        (nb090AlphaDummy181 h)), ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
        ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A),
        (nb090AlphaDummy173 h)), ((nb090AlphaDummy177 A), (nb090AlphaDummy178 h)),
        ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy051 A),
        (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A),
        (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A),
        (nb090AlphaDummy173 h)), ((nb090AlphaDummy177 A), (nb090AlphaDummy178 h)),
        ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy051 A),
        (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A),
        (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy181 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy186
        A) ≠ (nb090AlphaDummy197 A) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy187
        A) ≠ (nb090AlphaDummy199 A) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy187
        A) ≠ (nb090AlphaDummy199 A) from (by
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
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from
                                      (by
                                        unfold nb090AlphaDummy183;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0172 A)
                                                0)))) (show (nb090AlphaDummy181 h) ≠
                                        (nb090AlphaDummy184 h) from (by
                                        unfold nb090AlphaDummy184;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0173 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)),
                                    ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)),
                                    ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
                                    ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                                    ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                                    ((nb090AlphaDummy177 A), (nb090AlphaDummy178 h)),
                                    ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
                                    ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                    ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                    ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                    ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                                    ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                    ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                    ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                    ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                    ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from
                                    (by
                                      unfold nb090AlphaDummy183;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0172 A)
                                              0)))) (show
                                    (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from
                                    (by
                                      unfold nb090AlphaDummy184;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0173 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from
                                      (by
                                        unfold nb090AlphaDummy183;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0172 A)
                                                0)))) (show (nb090AlphaDummy181 h) ≠
                                        (nb090AlphaDummy184 h) from (by
                                        unfold nb090AlphaDummy184;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0173 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)),
                                    ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)),
                                    ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
                                    ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                                    ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                                    ((nb090AlphaDummy177 A), (nb090AlphaDummy178 h)),
                                    ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
                                    ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                    ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                    ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                    ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                                    ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                    ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                    ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                    ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                    ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy172 A) from (by
                        unfold nb090AlphaDummy172;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0164 A) 1))))
                    (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy174 h) from (by
                        unfold nb090AlphaDummy174;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0166 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy171 A) from (by
                          unfold nb090AlphaDummy171;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0164 A) 0))))
                      (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy173 h) from (by
                          unfold nb090AlphaDummy173;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0166 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy177 A) from (by
                            unfold nb090AlphaDummy177;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0168 A) 0))))
                        (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy178 h) from (by
                            unfold nb090AlphaDummy178;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0169 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy175 A) from (by
                              unfold nb090AlphaDummy175;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0165 A) 0))))
                          (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy176 h) from (by
                              unfold nb090AlphaDummy176;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0167 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy130 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy129 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy132 h))).fv ∪
                        ((Class.cv (nb090AlphaDummy131 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
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
                                      (mem_lt_freshVar (nb090_support_mem_0171 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy180 A) from
                                (by
                                  unfold nb090AlphaDummy180;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0170 A) 1))))
                              (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy182 h) from
                                (by
                                  unfold nb090AlphaDummy182;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0171 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy172 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy174 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy186 A) from (by
          unfold nb090AlphaDummy186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0174 A) 1)))) (show (nb090AlphaDummy181 h) ≠
        (nb090AlphaDummy189 h) from (by
          unfold nb090AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0175 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy185 A) from (by
          unfold nb090AlphaDummy185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0174 A)
                  0)))) (show (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy188 h) from (by
          unfold nb090AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0175 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy179 A) ≠
        (nb090AlphaDummy183 A) from (by
          unfold nb090AlphaDummy183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0172 A)
                  0)))) (show (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from (by
          unfold nb090AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0173 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy187 A), (nb090AlphaDummy190 h)), ((nb090AlphaDummy186 A),
        (nb090AlphaDummy189 h)), ((nb090AlphaDummy185 A), (nb090AlphaDummy188 h)),
        ((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)), ((nb090AlphaDummy179 A),
        (nb090AlphaDummy181 h)), ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
        ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A),
        (nb090AlphaDummy173 h)), ((nb090AlphaDummy177 A), (nb090AlphaDummy178 h)),
        ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy051 A),
        (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A),
        (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A),
        (nb090AlphaDummy173 h)), ((nb090AlphaDummy177 A), (nb090AlphaDummy178 h)),
        ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy051 A),
        (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A),
        (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy181
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy186
        A) ≠ (nb090AlphaDummy197 A) from (by
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
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy187
        A) ≠ (nb090AlphaDummy199 A) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy187
        A) ≠ (nb090AlphaDummy199 A) from (by
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
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A)
                                        from (by
                                          unfold nb090AlphaDummy183;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0172 A) 0)))) (show
                                        (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h)
                                        from (by
                                          unfold nb090AlphaDummy184;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0173 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)),
                                      ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)),
                                      ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
                                      ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                                      ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                                      ((nb090AlphaDummy177 A), (nb090AlphaDummy178 h)),
                                      ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
                                      ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                      ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                      ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
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
                                        (nb090AlphaDummy004 v u A h))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from
                                      (by
                                        unfold nb090AlphaDummy183;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0172 A)
                                                0)))) (show (nb090AlphaDummy181 h) ≠
                                        (nb090AlphaDummy184 h) from (by
                                        unfold nb090AlphaDummy184;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0173 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A)
                                        from (by
                                          unfold nb090AlphaDummy183;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0172 A) 0)))) (show
                                        (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h)
                                        from (by
                                          unfold nb090AlphaDummy184;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0173 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)),
                                      ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)),
                                      ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
                                      ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                                      ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                                      ((nb090AlphaDummy177 A), (nb090AlphaDummy178 h)),
                                      ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
                                      ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                      ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                      ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
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
                                        (nb090AlphaDummy004 v u A h))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part032`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0008`. -/
@[expose]
noncomputable def nb090SplitAlpha0008 (v : Var) (u : Var) (A : Class) (h : Var) :
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
        ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
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
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A),
        (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
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
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy051 A),
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
        ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A),
        (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A),
        (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
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

/-! Certificates from `NAR4C090C001Part033`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0009`. -/
@[expose]
noncomputable def nb090SplitAlpha0009 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy213 A), (nb090AlphaDummy214 h)),
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
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy213 A))
          (Class.cab (nb090AlphaDummy207 A)
            (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy051 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                (synCphi (Class.cv (nb090AlphaDummy208 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy213 A))
            (Class.cab (nb090AlphaDummy207 A)
              (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy051 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                  (synCphi (Class.cv (nb090AlphaDummy208 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy214 h))
          (Class.cab (nb090AlphaDummy209 h)
            (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy054 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                (synCphi (Class.cv (nb090AlphaDummy210 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy214 h))
            (Class.cab (nb090AlphaDummy209 h)
              (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy054 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                  (synCphi (Class.cv (nb090AlphaDummy210 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy208 A) from (by
                      unfold nb090AlphaDummy208;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0214 A) 1))))
                  (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy210 h) from (by
                      unfold nb090AlphaDummy210;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0216 h) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy207 A) from (by
                        unfold nb090AlphaDummy207;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0214 A) 0))))
                    (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy209 h) from (by
                        unfold nb090AlphaDummy209;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0216 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy213 A) from (by
                          unfold nb090AlphaDummy213;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0218 A) 0))))
                      (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy214 h) from (by
                          unfold nb090AlphaDummy214;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0219 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy211 A) from (by
                            unfold nb090AlphaDummy211;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0215 A) 0))))
                        (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy212 h) from (by
                            unfold nb090AlphaDummy212;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0217 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy051 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy050 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090AlphaDummy054 h))).fv ∪
                      ((Class.cv (nb090AlphaDummy053 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
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
        ((nb090AlphaDummy208 A), (nb090AlphaDummy210 h)), ((nb090AlphaDummy207 A),
        (nb090AlphaDummy209 h)), ((nb090AlphaDummy213 A), (nb090AlphaDummy214 h)),
        ((nb090AlphaDummy211 A), (nb090AlphaDummy212 h)), ((nb090AlphaDummy051 A),
        (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A),
        (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
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
        ((nb090AlphaDummy208 A), (nb090AlphaDummy210 h)), ((nb090AlphaDummy207 A),
        (nb090AlphaDummy209 h)), ((nb090AlphaDummy213 A), (nb090AlphaDummy214 h)),
        ((nb090AlphaDummy211 A), (nb090AlphaDummy212 h)), ((nb090AlphaDummy051 A),
        (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A),
        (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
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
                                    ((nb090AlphaDummy208 A), (nb090AlphaDummy210 h)),
                                    ((nb090AlphaDummy207 A), (nb090AlphaDummy209 h)),
                                    ((nb090AlphaDummy213 A), (nb090AlphaDummy214 h)),
                                    ((nb090AlphaDummy211 A), (nb090AlphaDummy212 h)),
                                    ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                                    ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                    ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                    ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                    ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                    ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
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
                                    ((nb090AlphaDummy208 A), (nb090AlphaDummy210 h)),
                                    ((nb090AlphaDummy207 A), (nb090AlphaDummy209 h)),
                                    ((nb090AlphaDummy213 A), (nb090AlphaDummy214 h)),
                                    ((nb090AlphaDummy211 A), (nb090AlphaDummy212 h)),
                                    ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                                    ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                    ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                    ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                    ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                    ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy208 A) from (by
                        unfold nb090AlphaDummy208;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0214 A) 1))))
                    (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy210 h) from (by
                        unfold nb090AlphaDummy210;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0216 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy207 A) from (by
                          unfold nb090AlphaDummy207;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0214 A) 0))))
                      (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy209 h) from (by
                          unfold nb090AlphaDummy209;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0216 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy213 A) from (by
                            unfold nb090AlphaDummy213;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0218 A) 0))))
                        (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy214 h) from (by
                            unfold nb090AlphaDummy214;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0219 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy211 A) from (by
                              unfold nb090AlphaDummy211;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0215 A) 0))))
                          (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy212 h) from (by
                              unfold nb090AlphaDummy212;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0217 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy051 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy050 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy054 h))).fv ∪
                        ((Class.cv (nb090AlphaDummy053 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
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
                                      (mem_lt_freshVar (nb090_support_mem_0221 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy208 A) ≠ (nb090AlphaDummy216 A) from
                                (by
                                  unfold nb090AlphaDummy216;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0220 A) 1))))
                              (show (nb090AlphaDummy210 h) ≠ (nb090AlphaDummy218 h) from
                                (by
                                  unfold nb090AlphaDummy218;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0221 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy208 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy210 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy222 A) from (by
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
                  (nb090_support_mem_0224 A)
                  0)))) (show (nb090AlphaDummy217 h) ≠ (nb090AlphaDummy224 h) from (by
          unfold nb090AlphaDummy224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0225 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy215 A) ≠
        (nb090AlphaDummy219 A) from (by
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
        ((nb090AlphaDummy208 A), (nb090AlphaDummy210 h)), ((nb090AlphaDummy207 A),
        (nb090AlphaDummy209 h)), ((nb090AlphaDummy213 A), (nb090AlphaDummy214 h)),
        ((nb090AlphaDummy211 A), (nb090AlphaDummy212 h)), ((nb090AlphaDummy051 A),
        (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A),
        (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
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
        (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        ((nb090AlphaDummy208 A), (nb090AlphaDummy210 h)), ((nb090AlphaDummy207 A),
        (nb090AlphaDummy209 h)), ((nb090AlphaDummy213 A), (nb090AlphaDummy214 h)),
        ((nb090AlphaDummy211 A), (nb090AlphaDummy212 h)), ((nb090AlphaDummy051 A),
        (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A),
        (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy215 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy217
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy215 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
        (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                                        (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy219 A)
                                        from (by
                                          unfold nb090AlphaDummy219;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0222 A) 0)))) (show
                                        (nb090AlphaDummy217 h) ≠ (nb090AlphaDummy220 h)
                                        from (by
                                          unfold nb090AlphaDummy220;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0223 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy219 A), (nb090AlphaDummy220 h)),
                                      ((nb090AlphaDummy215 A), (nb090AlphaDummy217 h)),
                                      ((nb090AlphaDummy216 A), (nb090AlphaDummy218 h)),
                                      ((nb090AlphaDummy208 A), (nb090AlphaDummy210 h)),
                                      ((nb090AlphaDummy207 A), (nb090AlphaDummy209 h)),
                                      ((nb090AlphaDummy213 A), (nb090AlphaDummy214 h)),
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
                                                0)))) (show (nb090AlphaDummy217 h) ≠
                                        (nb090AlphaDummy220 h) from (by
                                        unfold nb090AlphaDummy220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0223 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy219 A)
                                        from (by
                                          unfold nb090AlphaDummy219;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0222 A) 0)))) (show
                                        (nb090AlphaDummy217 h) ≠ (nb090AlphaDummy220 h)
                                        from (by
                                          unfold nb090AlphaDummy220;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0223 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy219 A), (nb090AlphaDummy220 h)),
                                      ((nb090AlphaDummy215 A), (nb090AlphaDummy217 h)),
                                      ((nb090AlphaDummy216 A), (nb090AlphaDummy218 h)),
                                      ((nb090AlphaDummy208 A), (nb090AlphaDummy210 h)),
                                      ((nb090AlphaDummy207 A), (nb090AlphaDummy209 h)),
                                      ((nb090AlphaDummy213 A), (nb090AlphaDummy214 h)),
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
                                        (nb090AlphaDummy004 v u A h))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
