/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block015

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part050`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0027`. -/
@[expose]
noncomputable def nb090SplitAlpha0027 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy177 A), (nb090AlphaDummy178 h)),
        ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
        ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
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
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy244 A),
        (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy186
        A) ≠ (nb090AlphaDummy193 A) from (by
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
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy244 A),
        (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy181
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
                                    ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
                                    ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
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
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy244 A),
        (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy186
        A) ≠ (nb090AlphaDummy193 A) from (by
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
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy244 A),
        (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy181
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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

/-! Certificates from `NAR4C090C001Part051`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0028`. -/
@[expose]
noncomputable def nb090SplitAlpha0028 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)),
        ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
        ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
        ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)),
        ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
        ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.classMem (Class.cv (nb090AlphaDummy203 A))
        (synCcompl (synCphi (Class.cv (nb090AlphaDummy172 A)))))
      (Wff.classMem (Class.cv (nb090AlphaDummy204 h))
        (synCcompl (synCphi (Class.cv (nb090AlphaDummy174 h))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                              (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy203 A) from
                                (by
                                  unfold nb090AlphaDummy203;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0198 A) 0))))
                              (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy204 h) from
                                (by
                                  unfold nb090AlphaDummy204;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0199 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb090AlphaDummy172 A))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb090AlphaDummy174 h))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
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
                  (nb090_support_mem_0172 A) 0)))) (show (nb090AlphaDummy181 h) ≠
        (nb090AlphaDummy184 h) from (by
          unfold nb090AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0173 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
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
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A),
        (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h),
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
        ((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)), ((nb090AlphaDummy203 A),
        (nb090AlphaDummy204 h)), ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
        ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)), ((nb090AlphaDummy201 A),
        (nb090AlphaDummy202 h)), ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A),
        (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A),
        (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h),
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
                                              0)))) (show
                                    (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from
                                    (by
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
                                  ((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)),
                                  ((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)),
                                  ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                                  ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                                  ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)),
                                  ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
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
                                  (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from (by
                                    unfold nb090AlphaDummy183;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0172 A)
                                            0)))) (show
                                  (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from (by
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
                                              0)))) (show
                                    (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from
                                    (by
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
                                  ((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)),
                                  ((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)),
                                  ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                                  ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                                  ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)),
                                  ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
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
                              (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy203 A) from
                                (by
                                  unfold nb090AlphaDummy203;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0198 A) 0))))
                              (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy204 h) from
                                (by
                                  unfold nb090AlphaDummy204;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0199 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb090AlphaDummy172 A))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb090AlphaDummy174 h))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
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
                  (nb090_support_mem_0172 A) 0)))) (show (nb090AlphaDummy181 h) ≠
        (nb090AlphaDummy184 h) from (by
          unfold nb090AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0173 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
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
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A),
        (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h),
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
        ((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)), ((nb090AlphaDummy203 A),
        (nb090AlphaDummy204 h)), ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
        ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)), ((nb090AlphaDummy201 A),
        (nb090AlphaDummy202 h)), ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A),
        (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A),
        (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h),
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
                                              0)))) (show
                                    (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from
                                    (by
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
                                  ((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)),
                                  ((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)),
                                  ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                                  ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                                  ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)),
                                  ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
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
                                  (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from (by
                                    unfold nb090AlphaDummy183;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0172 A)
                                            0)))) (show
                                  (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from (by
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
                                              0)))) (show
                                    (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from
                                    (by
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
                                  ((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)),
                                  ((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)),
                                  ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                                  ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                                  ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)),
                                  ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
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

theorem nb090_compact_fv_empty_0232 (A : Class) :
    (nb090AlphaDummy283 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0233 (u : Var) :
    (nb090AlphaDummy284 u) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0234 (A : Class) :
    (nb090AlphaDummy285 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0235 (u : Var) :
    (nb090AlphaDummy286 u) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0236 (A : Class) :
    (nb090AlphaDummy288 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0237 (u : Var) :
    (nb090AlphaDummy290 u) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0238 (A : Class) :
    (nb090AlphaDummy287 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0239 (u : Var) :
    (nb090AlphaDummy289 u) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
