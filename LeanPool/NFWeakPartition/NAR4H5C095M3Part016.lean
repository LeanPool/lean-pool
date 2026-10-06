/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part015

/-! NF weak partition development: NAR4H5C095M3Part016. -/


public section


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0020`. -/
@[expose]
noncomputable def nb095SplitAlpha0020 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy201 D R S_cls E), (nb095AlphaDummy202 f)),
        ((nb095AlphaDummy170 D R S_cls E), (nb095AlphaDummy172 f)),
        ((nb095AlphaDummy169 D R S_cls E), (nb095AlphaDummy171 f)),
        ((nb095AlphaDummy199 D R S_cls E), (nb095AlphaDummy200 f)),
        ((nb095AlphaDummy173 D R S_cls E), (nb095AlphaDummy174 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb095AlphaDummy201 D R S_cls E))
            (synCcompl (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))))
          (Wff.classMem (Class.cv (nb095AlphaDummy201 D R S_cls E))
            (synCcompl (synCsn (synC0c))))))
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb095AlphaDummy202 f))
            (synCcompl (synCphi (Class.cv (nb095AlphaDummy172 f)))))
          (Wff.classMem (Class.cv (nb095AlphaDummy202 f))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy170 D R S_cls E) ≠
                                (nb095AlphaDummy177 D R S_cls E) from (by
                                unfold nb095AlphaDummy177;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0178 D R S_cls E) 0))))
                            (show (nb095AlphaDummy172 f) ≠ (nb095AlphaDummy179 f) from (by
                                unfold nb095AlphaDummy179;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0179 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy170 D R S_cls E) ≠
                                  (nb095AlphaDummy178 D R S_cls E) from (by
                                  unfold nb095AlphaDummy178;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0178 D R S_cls E) 1))))
                              (show (nb095AlphaDummy172 f) ≠ (nb095AlphaDummy180 f) from
                                (by
                                  unfold nb095AlphaDummy180;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0179 f) 1))))
                              (TAlphaVar.there (show (nb095AlphaDummy170 D R S_cls E) ≠
                                    (nb095AlphaDummy203 D R S_cls E) from (by
                                    unfold nb095AlphaDummy203;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0208 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy172 f) ≠ (nb095AlphaDummy204 f) from (by
                                    unfold nb095AlphaDummy204;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0209 f)
                                            0)))) (TAlphaVar.there (show
                                    (nb095AlphaDummy170 D R S_cls E) ≠
                                      (nb095AlphaDummy201 D R S_cls E) from (by
                                      unfold nb095AlphaDummy201;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0206 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy172 f) ≠ (nb095AlphaDummy202 f) from
                                    (by
                                      unfold nb095AlphaDummy202;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0207 f)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy170 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy172 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy177 D R S_cls E) ≠ (nb095AlphaDummy184 D R S_cls E) from (by
          unfold nb095AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy187 f) from (by
          unfold nb095AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy177 D R S_cls E) ≠ (nb095AlphaDummy183 D R S_cls E) from (by
          unfold nb095AlphaDummy183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy186 f) from (by
          unfold nb095AlphaDummy186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy177 D R S_cls E) ≠
        (nb095AlphaDummy181 D R S_cls E) from (by
          unfold nb095AlphaDummy181;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0180 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy182 f) from (by
          unfold nb095AlphaDummy182;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0181 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy185 D R S_cls E), (nb095AlphaDummy188 f)),
        ((nb095AlphaDummy184 D R S_cls E), (nb095AlphaDummy187 f)),
        ((nb095AlphaDummy183 D R S_cls E), (nb095AlphaDummy186 f)),
        ((nb095AlphaDummy181 D R S_cls E), (nb095AlphaDummy182 f)),
        ((nb095AlphaDummy177 D R S_cls E), (nb095AlphaDummy179 f)),
        ((nb095AlphaDummy178 D R S_cls E), (nb095AlphaDummy180 f)),
        ((nb095AlphaDummy203 D R S_cls E), (nb095AlphaDummy204 f)),
        ((nb095AlphaDummy201 D R S_cls E), (nb095AlphaDummy202 f)),
        ((nb095AlphaDummy170 D R S_cls E), (nb095AlphaDummy172 f)),
        ((nb095AlphaDummy169 D R S_cls E), (nb095AlphaDummy171 f)),
        ((nb095AlphaDummy199 D R S_cls E), (nb095AlphaDummy200 f)),
        ((nb095AlphaDummy173 D R S_cls E), (nb095AlphaDummy174 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy184
        D R S_cls E) ≠ (nb095AlphaDummy191 D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0186
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy192 f) from (by
          unfold
            nb095AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠
        (nb095AlphaDummy189 D R S_cls E) from (by
          unfold
            nb095AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0184
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy190 f) from (by
          unfold
            nb095AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy177
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠ (nb095AlphaDummy191
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy192 f) from (by
          unfold
            nb095AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠
        (nb095AlphaDummy189 D R S_cls E) from (by
          unfold
            nb095AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0188
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy190 f) from (by
          unfold
            nb095AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠ (nb095AlphaDummy191
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0186
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy192 f) from (by
          unfold
            nb095AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠
        (nb095AlphaDummy189 D R S_cls E) from (by
          unfold
            nb095AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0184
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy190 f) from (by
          unfold
            nb095AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy177
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠ (nb095AlphaDummy191
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy192 f) from (by
          unfold
            nb095AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠
        (nb095AlphaDummy189 D R S_cls E) from (by
          unfold
            nb095AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0188
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy190 f) from (by
          unfold
            nb095AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy185 D R S_cls E), (nb095AlphaDummy188 f)),
        ((nb095AlphaDummy184 D R S_cls E), (nb095AlphaDummy187 f)),
        ((nb095AlphaDummy183 D R S_cls E), (nb095AlphaDummy186 f)),
        ((nb095AlphaDummy181 D R S_cls E), (nb095AlphaDummy182 f)),
        ((nb095AlphaDummy177 D R S_cls E), (nb095AlphaDummy179 f)),
        ((nb095AlphaDummy178 D R S_cls E), (nb095AlphaDummy180 f)),
        ((nb095AlphaDummy203 D R S_cls E), (nb095AlphaDummy204 f)),
        ((nb095AlphaDummy201 D R S_cls E), (nb095AlphaDummy202 f)),
        ((nb095AlphaDummy170 D R S_cls E), (nb095AlphaDummy172 f)),
        ((nb095AlphaDummy169 D R S_cls E), (nb095AlphaDummy171 f)),
        ((nb095AlphaDummy199 D R S_cls E), (nb095AlphaDummy200 f)),
        ((nb095AlphaDummy173 D R S_cls E), (nb095AlphaDummy174 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy177 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy177 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠ (nb095AlphaDummy195
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy196 f) from (by
          unfold
            nb095AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠
        (nb095AlphaDummy193 D R S_cls E) from (by
          unfold
            nb095AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0192
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy194 f) from (by
          unfold
            nb095AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy177
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠ (nb095AlphaDummy195
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy196 f) from (by
          unfold
            nb095AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠
        (nb095AlphaDummy193 D R S_cls E) from (by
          unfold
            nb095AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0192
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy194 f) from (by
          unfold
            nb095AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy177
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy185
        D R S_cls E) ≠ (nb095AlphaDummy197 D R S_cls E) from (by
          unfold
            nb095AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy198 f) from (by
          unfold
            nb095AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠
        (nb095AlphaDummy193 D R S_cls E) from (by
          unfold
            nb095AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0196
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy194 f) from (by
          unfold
            nb095AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy185
        D R S_cls E) ≠ (nb095AlphaDummy197 D R S_cls E) from (by
          unfold
            nb095AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy198 f) from (by
          unfold
            nb095AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠
        (nb095AlphaDummy193 D R S_cls E) from (by
          unfold
            nb095AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0196
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy194 f) from (by
          unfold
            nb095AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy177 D R S_cls E) ≠
        (nb095AlphaDummy181 D R S_cls E) from (by
                                          unfold nb095AlphaDummy181;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0180 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy179 f) ≠
        (nb095AlphaDummy182 f) from (by
                                          unfold nb095AlphaDummy182;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0181 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy181 D R S_cls E),
                                        (nb095AlphaDummy182 f)),
                                      ((nb095AlphaDummy177 D R S_cls E),
                                        (nb095AlphaDummy179 f)),
                                      ((nb095AlphaDummy178 D R S_cls E),
                                        (nb095AlphaDummy180 f)),
                                      ((nb095AlphaDummy203 D R S_cls E),
                                        (nb095AlphaDummy204 f)),
                                      ((nb095AlphaDummy201 D R S_cls E),
                                        (nb095AlphaDummy202 f)),
                                      ((nb095AlphaDummy170 D R S_cls E),
                                        (nb095AlphaDummy172 f)),
                                      ((nb095AlphaDummy169 D R S_cls E),
                                        (nb095AlphaDummy171 f)),
                                      ((nb095AlphaDummy199 D R S_cls E),
                                        (nb095AlphaDummy200 f)),
                                      ((nb095AlphaDummy173 D R S_cls E),
                                        (nb095AlphaDummy174 f)),
                                      ((nb095AlphaDummy013 D R S_cls E),
                                        (nb095AlphaDummy016 f)),
                                      ((nb095AlphaDummy012 D R S_cls E),
                                        (nb095AlphaDummy015 f)),
                                      ((nb095AlphaDummy011 D R S_cls E),
                                        (nb095AlphaDummy014 f)),
                                      ((nb095AlphaDummy017 D R S_cls E),
                                        (nb095AlphaDummy018 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy177 D R S_cls E) ≠
                                        (nb095AlphaDummy181 D R S_cls E) from (by
                                        unfold nb095AlphaDummy181;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy182 f) from
                                      (by
                                        unfold nb095AlphaDummy182;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0181 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy177 D R S_cls E) ≠
        (nb095AlphaDummy181 D R S_cls E) from (by
                                          unfold nb095AlphaDummy181;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0180 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy179 f) ≠
        (nb095AlphaDummy182 f) from (by
                                          unfold nb095AlphaDummy182;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0181 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy181 D R S_cls E),
                                        (nb095AlphaDummy182 f)),
                                      ((nb095AlphaDummy177 D R S_cls E),
                                        (nb095AlphaDummy179 f)),
                                      ((nb095AlphaDummy178 D R S_cls E),
                                        (nb095AlphaDummy180 f)),
                                      ((nb095AlphaDummy203 D R S_cls E),
                                        (nb095AlphaDummy204 f)),
                                      ((nb095AlphaDummy201 D R S_cls E),
                                        (nb095AlphaDummy202 f)),
                                      ((nb095AlphaDummy170 D R S_cls E),
                                        (nb095AlphaDummy172 f)),
                                      ((nb095AlphaDummy169 D R S_cls E),
                                        (nb095AlphaDummy171 f)),
                                      ((nb095AlphaDummy199 D R S_cls E),
                                        (nb095AlphaDummy200 f)),
                                      ((nb095AlphaDummy173 D R S_cls E),
                                        (nb095AlphaDummy174 f)),
                                      ((nb095AlphaDummy013 D R S_cls E),
                                        (nb095AlphaDummy016 f)),
                                      ((nb095AlphaDummy012 D R S_cls E),
                                        (nb095AlphaDummy015 f)),
                                      ((nb095AlphaDummy011 D R S_cls E),
                                        (nb095AlphaDummy014 f)),
                                      ((nb095AlphaDummy017 D R S_cls E),
                                        (nb095AlphaDummy018 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy170 D R S_cls E) ≠
                                (nb095AlphaDummy177 D R S_cls E) from (by
                                unfold nb095AlphaDummy177;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0178 D R S_cls E) 0))))
                            (show (nb095AlphaDummy172 f) ≠ (nb095AlphaDummy179 f) from (by
                                unfold nb095AlphaDummy179;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0179 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy170 D R S_cls E) ≠
                                  (nb095AlphaDummy178 D R S_cls E) from (by
                                  unfold nb095AlphaDummy178;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0178 D R S_cls E) 1))))
                              (show (nb095AlphaDummy172 f) ≠ (nb095AlphaDummy180 f) from
                                (by
                                  unfold nb095AlphaDummy180;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0179 f) 1))))
                              (TAlphaVar.there (show (nb095AlphaDummy170 D R S_cls E) ≠
                                    (nb095AlphaDummy203 D R S_cls E) from (by
                                    unfold nb095AlphaDummy203;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0208 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy172 f) ≠ (nb095AlphaDummy204 f) from (by
                                    unfold nb095AlphaDummy204;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0209 f)
                                            0)))) (TAlphaVar.there (show
                                    (nb095AlphaDummy170 D R S_cls E) ≠
                                      (nb095AlphaDummy201 D R S_cls E) from (by
                                      unfold nb095AlphaDummy201;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0206 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy172 f) ≠ (nb095AlphaDummy202 f) from
                                    (by
                                      unfold nb095AlphaDummy202;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0207 f)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy170 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy172 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy177 D R S_cls E) ≠ (nb095AlphaDummy184 D R S_cls E) from (by
          unfold nb095AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy187 f) from (by
          unfold nb095AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy177 D R S_cls E) ≠ (nb095AlphaDummy183 D R S_cls E) from (by
          unfold nb095AlphaDummy183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy186 f) from (by
          unfold nb095AlphaDummy186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy177 D R S_cls E) ≠
        (nb095AlphaDummy181 D R S_cls E) from (by
          unfold nb095AlphaDummy181;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0180 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy182 f) from (by
          unfold nb095AlphaDummy182;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0181 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy185 D R S_cls E), (nb095AlphaDummy188 f)),
        ((nb095AlphaDummy184 D R S_cls E), (nb095AlphaDummy187 f)),
        ((nb095AlphaDummy183 D R S_cls E), (nb095AlphaDummy186 f)),
        ((nb095AlphaDummy181 D R S_cls E), (nb095AlphaDummy182 f)),
        ((nb095AlphaDummy177 D R S_cls E), (nb095AlphaDummy179 f)),
        ((nb095AlphaDummy178 D R S_cls E), (nb095AlphaDummy180 f)),
        ((nb095AlphaDummy203 D R S_cls E), (nb095AlphaDummy204 f)),
        ((nb095AlphaDummy201 D R S_cls E), (nb095AlphaDummy202 f)),
        ((nb095AlphaDummy170 D R S_cls E), (nb095AlphaDummy172 f)),
        ((nb095AlphaDummy169 D R S_cls E), (nb095AlphaDummy171 f)),
        ((nb095AlphaDummy199 D R S_cls E), (nb095AlphaDummy200 f)),
        ((nb095AlphaDummy173 D R S_cls E), (nb095AlphaDummy174 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy184
        D R S_cls E) ≠ (nb095AlphaDummy191 D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0186
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy192 f) from (by
          unfold
            nb095AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠
        (nb095AlphaDummy189 D R S_cls E) from (by
          unfold
            nb095AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0184
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy190 f) from (by
          unfold
            nb095AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy177
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠ (nb095AlphaDummy191
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy192 f) from (by
          unfold
            nb095AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠
        (nb095AlphaDummy189 D R S_cls E) from (by
          unfold
            nb095AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0188
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy190 f) from (by
          unfold
            nb095AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠ (nb095AlphaDummy191
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0186
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy192 f) from (by
          unfold
            nb095AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠
        (nb095AlphaDummy189 D R S_cls E) from (by
          unfold
            nb095AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0184
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy190 f) from (by
          unfold
            nb095AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy177
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠ (nb095AlphaDummy191
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy192 f) from (by
          unfold
            nb095AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠
        (nb095AlphaDummy189 D R S_cls E) from (by
          unfold
            nb095AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0188
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy190 f) from (by
          unfold
            nb095AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy185 D R S_cls E), (nb095AlphaDummy188 f)),
        ((nb095AlphaDummy184 D R S_cls E), (nb095AlphaDummy187 f)),
        ((nb095AlphaDummy183 D R S_cls E), (nb095AlphaDummy186 f)),
        ((nb095AlphaDummy181 D R S_cls E), (nb095AlphaDummy182 f)),
        ((nb095AlphaDummy177 D R S_cls E), (nb095AlphaDummy179 f)),
        ((nb095AlphaDummy178 D R S_cls E), (nb095AlphaDummy180 f)),
        ((nb095AlphaDummy203 D R S_cls E), (nb095AlphaDummy204 f)),
        ((nb095AlphaDummy201 D R S_cls E), (nb095AlphaDummy202 f)),
        ((nb095AlphaDummy170 D R S_cls E), (nb095AlphaDummy172 f)),
        ((nb095AlphaDummy169 D R S_cls E), (nb095AlphaDummy171 f)),
        ((nb095AlphaDummy199 D R S_cls E), (nb095AlphaDummy200 f)),
        ((nb095AlphaDummy173 D R S_cls E), (nb095AlphaDummy174 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy177 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy177 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠ (nb095AlphaDummy195
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy196 f) from (by
          unfold
            nb095AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠
        (nb095AlphaDummy193 D R S_cls E) from (by
          unfold
            nb095AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0192
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy194 f) from (by
          unfold
            nb095AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy177
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠ (nb095AlphaDummy195
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy196 f) from (by
          unfold
            nb095AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠
        (nb095AlphaDummy193 D R S_cls E) from (by
          unfold
            nb095AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0192
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy194 f) from (by
          unfold
            nb095AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy177
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy185
        D R S_cls E) ≠ (nb095AlphaDummy197 D R S_cls E) from (by
          unfold
            nb095AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy198 f) from (by
          unfold
            nb095AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠
        (nb095AlphaDummy193 D R S_cls E) from (by
          unfold
            nb095AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0196
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy194 f) from (by
          unfold
            nb095AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy185
        D R S_cls E) ≠ (nb095AlphaDummy197 D R S_cls E) from (by
          unfold
            nb095AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy198 f) from (by
          unfold
            nb095AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠
        (nb095AlphaDummy193 D R S_cls E) from (by
          unfold
            nb095AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0196
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy194 f) from (by
          unfold
            nb095AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy177 D R S_cls E) ≠
        (nb095AlphaDummy181 D R S_cls E) from (by
                                          unfold nb095AlphaDummy181;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0180 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy179 f) ≠
        (nb095AlphaDummy182 f) from (by
                                          unfold nb095AlphaDummy182;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0181 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy181 D R S_cls E),
                                        (nb095AlphaDummy182 f)),
                                      ((nb095AlphaDummy177 D R S_cls E),
                                        (nb095AlphaDummy179 f)),
                                      ((nb095AlphaDummy178 D R S_cls E),
                                        (nb095AlphaDummy180 f)),
                                      ((nb095AlphaDummy203 D R S_cls E),
                                        (nb095AlphaDummy204 f)),
                                      ((nb095AlphaDummy201 D R S_cls E),
                                        (nb095AlphaDummy202 f)),
                                      ((nb095AlphaDummy170 D R S_cls E),
                                        (nb095AlphaDummy172 f)),
                                      ((nb095AlphaDummy169 D R S_cls E),
                                        (nb095AlphaDummy171 f)),
                                      ((nb095AlphaDummy199 D R S_cls E),
                                        (nb095AlphaDummy200 f)),
                                      ((nb095AlphaDummy173 D R S_cls E),
                                        (nb095AlphaDummy174 f)),
                                      ((nb095AlphaDummy013 D R S_cls E),
                                        (nb095AlphaDummy016 f)),
                                      ((nb095AlphaDummy012 D R S_cls E),
                                        (nb095AlphaDummy015 f)),
                                      ((nb095AlphaDummy011 D R S_cls E),
                                        (nb095AlphaDummy014 f)),
                                      ((nb095AlphaDummy017 D R S_cls E),
                                        (nb095AlphaDummy018 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy177 D R S_cls E) ≠
                                        (nb095AlphaDummy181 D R S_cls E) from (by
                                        unfold nb095AlphaDummy181;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy182 f) from
                                      (by
                                        unfold nb095AlphaDummy182;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0181 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy177 D R S_cls E) ≠
        (nb095AlphaDummy181 D R S_cls E) from (by
                                          unfold nb095AlphaDummy181;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0180 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy179 f) ≠
        (nb095AlphaDummy182 f) from (by
                                          unfold nb095AlphaDummy182;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0181 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy181 D R S_cls E),
                                        (nb095AlphaDummy182 f)),
                                      ((nb095AlphaDummy177 D R S_cls E),
                                        (nb095AlphaDummy179 f)),
                                      ((nb095AlphaDummy178 D R S_cls E),
                                        (nb095AlphaDummy180 f)),
                                      ((nb095AlphaDummy203 D R S_cls E),
                                        (nb095AlphaDummy204 f)),
                                      ((nb095AlphaDummy201 D R S_cls E),
                                        (nb095AlphaDummy202 f)),
                                      ((nb095AlphaDummy170 D R S_cls E),
                                        (nb095AlphaDummy172 f)),
                                      ((nb095AlphaDummy169 D R S_cls E),
                                        (nb095AlphaDummy171 f)),
                                      ((nb095AlphaDummy199 D R S_cls E),
                                        (nb095AlphaDummy200 f)),
                                      ((nb095AlphaDummy173 D R S_cls E),
                                        (nb095AlphaDummy174 f)),
                                      ((nb095AlphaDummy013 D R S_cls E),
                                        (nb095AlphaDummy016 f)),
                                      ((nb095AlphaDummy012 D R S_cls E),
                                        (nb095AlphaDummy015 f)),
                                      ((nb095AlphaDummy011 D R S_cls E),
                                        (nb095AlphaDummy014 f)),
                                      ((nb095AlphaDummy017 D R S_cls E),
                                        (nb095AlphaDummy018 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
          [((nb095AlphaDummy201 D R S_cls E), (nb095AlphaDummy202 f)),
            ((nb095AlphaDummy170 D R S_cls E), (nb095AlphaDummy172 f)),
            ((nb095AlphaDummy169 D R S_cls E), (nb095AlphaDummy171 f)),
            ((nb095AlphaDummy199 D R S_cls E), (nb095AlphaDummy200 f)),
            ((nb095AlphaDummy173 D R S_cls E), (nb095AlphaDummy174 f)),
            ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
            ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
            ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
            ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
            ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
            ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0021`. -/
@[expose]
noncomputable def nb095SplitAlpha0021 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy210 D R S_cls E), (nb095AlphaDummy212 f)),
        ((nb095AlphaDummy209 D R S_cls E), (nb095AlphaDummy211 f)),
        ((nb095AlphaDummy239 D R S_cls E), (nb095AlphaDummy240 f)),
        ((nb095AlphaDummy213 D R S_cls E), (nb095AlphaDummy214 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy210 D R S_cls E))
          (Class.cv (nb095AlphaDummy205 D R S_cls E))) (Wff.neg
          (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
            (synCun (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))
              (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy212 f))
          (Class.cv (nb095AlphaDummy207 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
            (synCun (synCphi (Class.cv (nb095AlphaDummy212 f))) (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there
          (show (nb095AlphaDummy205 D R S_cls E) ≠ (nb095AlphaDummy210 D R S_cls E) from
            (by
              unfold nb095AlphaDummy210;
              with_reducible
                exact
                  (Nat.ne_of_lt
                    (mem_lt_freshVar (nb095_support_mem_0238 D R S_cls E) 1))))
          (show (nb095AlphaDummy207 f) ≠ (nb095AlphaDummy212 f) from (by
              unfold nb095AlphaDummy212;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0240 f) 1))))
          (TAlphaVar.there (show
              (nb095AlphaDummy205 D R S_cls E) ≠ (nb095AlphaDummy209 D R S_cls E) from (by
                unfold nb095AlphaDummy209;
                with_reducible
                  exact
                    (Nat.ne_of_lt
                      (mem_lt_freshVar (nb095_support_mem_0238 D R S_cls E) 0))))
            (show (nb095AlphaDummy207 f) ≠ (nb095AlphaDummy211 f) from (by
                unfold nb095AlphaDummy211;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0240 f) 0))))
            (TAlphaVar.there (show
                (nb095AlphaDummy205 D R S_cls E) ≠ (nb095AlphaDummy239 D R S_cls E) from
                (by
                  unfold nb095AlphaDummy239;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb095_support_mem_0242 D R S_cls E) 0))))
              (show (nb095AlphaDummy207 f) ≠ (nb095AlphaDummy240 f) from (by
                  unfold nb095AlphaDummy240;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0243 f) 0))))
              (TAlphaVar.there (show (nb095AlphaDummy205 D R S_cls E) ≠
                    (nb095AlphaDummy213 D R S_cls E) from (by
                    unfold nb095AlphaDummy213;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb095_support_mem_0239 D R S_cls E) 0))))
                (show (nb095AlphaDummy207 f) ≠ (nb095AlphaDummy214 f) from (by
                    unfold nb095AlphaDummy214;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0241 f) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪
                      ((synCvv)).fv) (by decide))
                  (freshVar_injective (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv)
                    (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb095AlphaDummy206 D R S_cls E))).fv ∪
                ((Class.cv (nb095AlphaDummy205 D R S_cls E))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb095AlphaDummy208 f))).fv ∪
                ((Class.cv (nb095AlphaDummy207 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy210 D R S_cls E) ≠
                                        (nb095AlphaDummy217 D R S_cls E) from (by
                                        unfold nb095AlphaDummy217;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0216 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy212 f) ≠ (nb095AlphaDummy219 f) from
                                      (by
                                        unfold nb095AlphaDummy219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0217 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy210 D R S_cls E) ≠
        (nb095AlphaDummy218 D R S_cls E) from (by
                                          unfold nb095AlphaDummy218;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0216 D R S_cls E)
                                                  1)))) (show (nb095AlphaDummy212 f) ≠
        (nb095AlphaDummy220 f) from (by
                                          unfold nb095AlphaDummy220;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0217 f) 1))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy210 D R S_cls E) ≠ (nb095AlphaDummy243 D R S_cls E) from (by
          unfold nb095AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0246 D R S_cls E)
                  0)))) (show (nb095AlphaDummy212 f) ≠ (nb095AlphaDummy244 f) from (by
          unfold nb095AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0247 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy210 D R S_cls E) ≠ (nb095AlphaDummy241 D R S_cls E) from (by
          unfold nb095AlphaDummy241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0244 D R S_cls E)
                  0)))) (show (nb095AlphaDummy212 f) ≠ (nb095AlphaDummy242 f) from (by
          unfold nb095AlphaDummy242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0245 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective (((Class.cv
        (nb095AlphaDummy210 D R S_cls E))).fv) (by decide)) (freshVar_injective
                                      (((Class.cv (nb095AlphaDummy212 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy217 D R S_cls E) ≠
        (nb095AlphaDummy224 D R S_cls E) from (by
          unfold nb095AlphaDummy224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0220
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy227 f) from (by
          unfold nb095AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0221
                    f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy217 D R S_cls E) ≠
        (nb095AlphaDummy223 D R S_cls E) from (by
          unfold nb095AlphaDummy223;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0220
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy226 f) from (by
          unfold nb095AlphaDummy226;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0221
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy217 D R S_cls E) ≠
        (nb095AlphaDummy221 D R S_cls E) from (by
          unfold
            nb095AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy222 f) from (by
          unfold
            nb095AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy225 D R S_cls E), (nb095AlphaDummy228 f)),
        ((nb095AlphaDummy224 D R S_cls E), (nb095AlphaDummy227 f)),
        ((nb095AlphaDummy223 D R S_cls E), (nb095AlphaDummy226 f)),
        ((nb095AlphaDummy221 D R S_cls E), (nb095AlphaDummy222 f)),
        ((nb095AlphaDummy217 D R S_cls E), (nb095AlphaDummy219 f)),
        ((nb095AlphaDummy218 D R S_cls E), (nb095AlphaDummy220 f)),
        ((nb095AlphaDummy243 D R S_cls E), (nb095AlphaDummy244 f)),
        ((nb095AlphaDummy241 D R S_cls E), (nb095AlphaDummy242 f)),
        ((nb095AlphaDummy210 D R S_cls E), (nb095AlphaDummy212 f)),
        ((nb095AlphaDummy209 D R S_cls E), (nb095AlphaDummy211 f)),
        ((nb095AlphaDummy239 D R S_cls E), (nb095AlphaDummy240 f)),
        ((nb095AlphaDummy213 D R S_cls E), (nb095AlphaDummy214 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠
        (nb095AlphaDummy231 D R S_cls E) from (by
          unfold
            nb095AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0224
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy232 f) from (by
          unfold
            nb095AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠
        (nb095AlphaDummy229 D R S_cls E) from (by
          unfold
            nb095AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0222
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy230 f) from (by
          unfold
            nb095AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy217
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy225
        D R S_cls E) ≠ (nb095AlphaDummy231 D R S_cls E) from (by
          unfold
            nb095AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0228
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy232 f) from (by
          unfold
            nb095AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy225 D R S_cls E) ≠
        (nb095AlphaDummy229 D R S_cls E) from (by
          unfold
            nb095AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0226
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy230 f) from (by
          unfold
            nb095AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠ (nb095AlphaDummy231 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0224
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy232 f) from (by
          unfold
            nb095AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠
        (nb095AlphaDummy229 D R S_cls E) from (by
          unfold
            nb095AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0222
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy230 f) from (by
          unfold
            nb095AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy217
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy225
        D R S_cls E) ≠ (nb095AlphaDummy231 D R S_cls E) from (by
          unfold
            nb095AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0228
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy232 f) from (by
          unfold
            nb095AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy225 D R S_cls E) ≠
        (nb095AlphaDummy229 D R S_cls E) from (by
          unfold
            nb095AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0226
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy230 f) from (by
          unfold
            nb095AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy225 D R S_cls E), (nb095AlphaDummy228 f)),
        ((nb095AlphaDummy224 D R S_cls E), (nb095AlphaDummy227 f)),
        ((nb095AlphaDummy223 D R S_cls E), (nb095AlphaDummy226 f)),
        ((nb095AlphaDummy221 D R S_cls E), (nb095AlphaDummy222 f)),
        ((nb095AlphaDummy217 D R S_cls E), (nb095AlphaDummy219 f)),
        ((nb095AlphaDummy218 D R S_cls E), (nb095AlphaDummy220 f)),
        ((nb095AlphaDummy243 D R S_cls E), (nb095AlphaDummy244 f)),
        ((nb095AlphaDummy241 D R S_cls E), (nb095AlphaDummy242 f)),
        ((nb095AlphaDummy210 D R S_cls E), (nb095AlphaDummy212 f)),
        ((nb095AlphaDummy209 D R S_cls E), (nb095AlphaDummy211 f)),
        ((nb095AlphaDummy239 D R S_cls E), (nb095AlphaDummy240 f)),
        ((nb095AlphaDummy213 D R S_cls E), (nb095AlphaDummy214 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy217 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy217
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy219 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠ (nb095AlphaDummy235 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0232
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy236 f) from (by
          unfold
            nb095AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠
        (nb095AlphaDummy233 D R S_cls E) from (by
          unfold
            nb095AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0230
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy234 f) from (by
          unfold
            nb095AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy217
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy224
        D R S_cls E) ≠ (nb095AlphaDummy235 D R S_cls E) from (by
          unfold
            nb095AlphaDummy235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0232
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy236 f) from (by
          unfold
            nb095AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠
        (nb095AlphaDummy233 D R S_cls E) from (by
          unfold
            nb095AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0230
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy234 f) from (by
          unfold
            nb095AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy217
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy225 D R S_cls E) ≠ (nb095AlphaDummy237 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0236
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy238 f) from (by
          unfold
            nb095AlphaDummy238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy225 D R S_cls E) ≠
        (nb095AlphaDummy233 D R S_cls E) from (by
          unfold
            nb095AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0234
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy234 f) from (by
          unfold
            nb095AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy225
        D R S_cls E) ≠ (nb095AlphaDummy237 D R S_cls E) from (by
          unfold
            nb095AlphaDummy237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0236
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy238 f) from (by
          unfold
            nb095AlphaDummy238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy225 D R S_cls E) ≠
        (nb095AlphaDummy233 D R S_cls E) from (by
          unfold
            nb095AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0234
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy234 f) from (by
          unfold
            nb095AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy217 D R S_cls E) ≠
        (nb095AlphaDummy221 D R S_cls E) from (by
          unfold nb095AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy222 f) from (by
          unfold nb095AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb095AlphaDummy221 D R S_cls E),
        (nb095AlphaDummy222 f)), ((nb095AlphaDummy217 D R S_cls E),
        (nb095AlphaDummy219 f)), ((nb095AlphaDummy218 D R S_cls E),
        (nb095AlphaDummy220 f)), ((nb095AlphaDummy243 D R S_cls E),
        (nb095AlphaDummy244 f)), ((nb095AlphaDummy241 D R S_cls E),
        (nb095AlphaDummy242 f)), ((nb095AlphaDummy210 D R S_cls E),
        (nb095AlphaDummy212 f)), ((nb095AlphaDummy209 D R S_cls E),
        (nb095AlphaDummy211 f)), ((nb095AlphaDummy239 D R S_cls E),
        (nb095AlphaDummy240 f)), ((nb095AlphaDummy213 D R S_cls E),
        (nb095AlphaDummy214 f)), ((nb095AlphaDummy206 D R S_cls E),
        (nb095AlphaDummy208 f)), ((nb095AlphaDummy205 D R S_cls E),
        (nb095AlphaDummy207 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy217 D R S_cls E) ≠
        (nb095AlphaDummy221 D R S_cls E) from (by
          unfold nb095AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy222 f) from (by
          unfold nb095AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb095AlphaDummy217 D R S_cls E) ≠ (nb095AlphaDummy221 D R S_cls E) from (by
          unfold nb095AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy222 f) from (by
          unfold nb095AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb095AlphaDummy221 D R S_cls E),
        (nb095AlphaDummy222 f)), ((nb095AlphaDummy217 D R S_cls E),
        (nb095AlphaDummy219 f)), ((nb095AlphaDummy218 D R S_cls E),
        (nb095AlphaDummy220 f)), ((nb095AlphaDummy243 D R S_cls E),
        (nb095AlphaDummy244 f)), ((nb095AlphaDummy241 D R S_cls E),
        (nb095AlphaDummy242 f)), ((nb095AlphaDummy210 D R S_cls E),
        (nb095AlphaDummy212 f)), ((nb095AlphaDummy209 D R S_cls E),
        (nb095AlphaDummy211 f)), ((nb095AlphaDummy239 D R S_cls E),
        (nb095AlphaDummy240 f)), ((nb095AlphaDummy213 D R S_cls E),
        (nb095AlphaDummy214 f)), ((nb095AlphaDummy206 D R S_cls E),
        (nb095AlphaDummy208 f)), ((nb095AlphaDummy205 D R S_cls E),
        (nb095AlphaDummy207 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy210 D R S_cls E) ≠
                                        (nb095AlphaDummy217 D R S_cls E) from (by
                                        unfold nb095AlphaDummy217;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0216 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy212 f) ≠ (nb095AlphaDummy219 f) from
                                      (by
                                        unfold nb095AlphaDummy219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0217 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy210 D R S_cls E) ≠
        (nb095AlphaDummy218 D R S_cls E) from (by
                                          unfold nb095AlphaDummy218;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0216 D R S_cls E)
                                                  1)))) (show (nb095AlphaDummy212 f) ≠
        (nb095AlphaDummy220 f) from (by
                                          unfold nb095AlphaDummy220;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0217 f) 1))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy210 D R S_cls E) ≠ (nb095AlphaDummy243 D R S_cls E) from (by
          unfold nb095AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0246 D R S_cls E)
                  0)))) (show (nb095AlphaDummy212 f) ≠ (nb095AlphaDummy244 f) from (by
          unfold nb095AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0247 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy210 D R S_cls E) ≠ (nb095AlphaDummy241 D R S_cls E) from (by
          unfold nb095AlphaDummy241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0244 D R S_cls E)
                  0)))) (show (nb095AlphaDummy212 f) ≠ (nb095AlphaDummy242 f) from (by
          unfold nb095AlphaDummy242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0245 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective (((Class.cv
        (nb095AlphaDummy210 D R S_cls E))).fv) (by decide)) (freshVar_injective
                                      (((Class.cv (nb095AlphaDummy212 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy217 D R S_cls E) ≠
        (nb095AlphaDummy224 D R S_cls E) from (by
          unfold nb095AlphaDummy224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0220
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy227 f) from (by
          unfold nb095AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0221
                    f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy217 D R S_cls E) ≠
        (nb095AlphaDummy223 D R S_cls E) from (by
          unfold nb095AlphaDummy223;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0220
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy226 f) from (by
          unfold nb095AlphaDummy226;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0221
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy217 D R S_cls E) ≠
        (nb095AlphaDummy221 D R S_cls E) from (by
          unfold
            nb095AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy222 f) from (by
          unfold
            nb095AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy225 D R S_cls E), (nb095AlphaDummy228 f)),
        ((nb095AlphaDummy224 D R S_cls E), (nb095AlphaDummy227 f)),
        ((nb095AlphaDummy223 D R S_cls E), (nb095AlphaDummy226 f)),
        ((nb095AlphaDummy221 D R S_cls E), (nb095AlphaDummy222 f)),
        ((nb095AlphaDummy217 D R S_cls E), (nb095AlphaDummy219 f)),
        ((nb095AlphaDummy218 D R S_cls E), (nb095AlphaDummy220 f)),
        ((nb095AlphaDummy243 D R S_cls E), (nb095AlphaDummy244 f)),
        ((nb095AlphaDummy241 D R S_cls E), (nb095AlphaDummy242 f)),
        ((nb095AlphaDummy210 D R S_cls E), (nb095AlphaDummy212 f)),
        ((nb095AlphaDummy209 D R S_cls E), (nb095AlphaDummy211 f)),
        ((nb095AlphaDummy239 D R S_cls E), (nb095AlphaDummy240 f)),
        ((nb095AlphaDummy213 D R S_cls E), (nb095AlphaDummy214 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠
        (nb095AlphaDummy231 D R S_cls E) from (by
          unfold
            nb095AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0224
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy232 f) from (by
          unfold
            nb095AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠
        (nb095AlphaDummy229 D R S_cls E) from (by
          unfold
            nb095AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0222
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy230 f) from (by
          unfold
            nb095AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy217
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy225
        D R S_cls E) ≠ (nb095AlphaDummy231 D R S_cls E) from (by
          unfold
            nb095AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0228
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy232 f) from (by
          unfold
            nb095AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy225 D R S_cls E) ≠
        (nb095AlphaDummy229 D R S_cls E) from (by
          unfold
            nb095AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0226
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy230 f) from (by
          unfold
            nb095AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠ (nb095AlphaDummy231 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0224
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy232 f) from (by
          unfold
            nb095AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠
        (nb095AlphaDummy229 D R S_cls E) from (by
          unfold
            nb095AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0222
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy230 f) from (by
          unfold
            nb095AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy217
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy225
        D R S_cls E) ≠ (nb095AlphaDummy231 D R S_cls E) from (by
          unfold
            nb095AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0228
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy232 f) from (by
          unfold
            nb095AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy225 D R S_cls E) ≠
        (nb095AlphaDummy229 D R S_cls E) from (by
          unfold
            nb095AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0226
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy230 f) from (by
          unfold
            nb095AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy225 D R S_cls E), (nb095AlphaDummy228 f)),
        ((nb095AlphaDummy224 D R S_cls E), (nb095AlphaDummy227 f)),
        ((nb095AlphaDummy223 D R S_cls E), (nb095AlphaDummy226 f)),
        ((nb095AlphaDummy221 D R S_cls E), (nb095AlphaDummy222 f)),
        ((nb095AlphaDummy217 D R S_cls E), (nb095AlphaDummy219 f)),
        ((nb095AlphaDummy218 D R S_cls E), (nb095AlphaDummy220 f)),
        ((nb095AlphaDummy243 D R S_cls E), (nb095AlphaDummy244 f)),
        ((nb095AlphaDummy241 D R S_cls E), (nb095AlphaDummy242 f)),
        ((nb095AlphaDummy210 D R S_cls E), (nb095AlphaDummy212 f)),
        ((nb095AlphaDummy209 D R S_cls E), (nb095AlphaDummy211 f)),
        ((nb095AlphaDummy239 D R S_cls E), (nb095AlphaDummy240 f)),
        ((nb095AlphaDummy213 D R S_cls E), (nb095AlphaDummy214 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy217 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy217
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy219 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠ (nb095AlphaDummy235 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0232
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy236 f) from (by
          unfold
            nb095AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠
        (nb095AlphaDummy233 D R S_cls E) from (by
          unfold
            nb095AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0230
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy234 f) from (by
          unfold
            nb095AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy217
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy224
        D R S_cls E) ≠ (nb095AlphaDummy235 D R S_cls E) from (by
          unfold
            nb095AlphaDummy235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0232
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy236 f) from (by
          unfold
            nb095AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠
        (nb095AlphaDummy233 D R S_cls E) from (by
          unfold
            nb095AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0230
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy234 f) from (by
          unfold
            nb095AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy217
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy225 D R S_cls E) ≠ (nb095AlphaDummy237 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0236
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy238 f) from (by
          unfold
            nb095AlphaDummy238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy225 D R S_cls E) ≠
        (nb095AlphaDummy233 D R S_cls E) from (by
          unfold
            nb095AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0234
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy234 f) from (by
          unfold
            nb095AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy225
        D R S_cls E) ≠ (nb095AlphaDummy237 D R S_cls E) from (by
          unfold
            nb095AlphaDummy237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0236
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy238 f) from (by
          unfold
            nb095AlphaDummy238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy225 D R S_cls E) ≠
        (nb095AlphaDummy233 D R S_cls E) from (by
          unfold
            nb095AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0234
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy234 f) from (by
          unfold
            nb095AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy217 D R S_cls E) ≠
        (nb095AlphaDummy221 D R S_cls E) from (by
          unfold nb095AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy222 f) from (by
          unfold nb095AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb095AlphaDummy221 D R S_cls E),
        (nb095AlphaDummy222 f)), ((nb095AlphaDummy217 D R S_cls E),
        (nb095AlphaDummy219 f)), ((nb095AlphaDummy218 D R S_cls E),
        (nb095AlphaDummy220 f)), ((nb095AlphaDummy243 D R S_cls E),
        (nb095AlphaDummy244 f)), ((nb095AlphaDummy241 D R S_cls E),
        (nb095AlphaDummy242 f)), ((nb095AlphaDummy210 D R S_cls E),
        (nb095AlphaDummy212 f)), ((nb095AlphaDummy209 D R S_cls E),
        (nb095AlphaDummy211 f)), ((nb095AlphaDummy239 D R S_cls E),
        (nb095AlphaDummy240 f)), ((nb095AlphaDummy213 D R S_cls E),
        (nb095AlphaDummy214 f)), ((nb095AlphaDummy206 D R S_cls E),
        (nb095AlphaDummy208 f)), ((nb095AlphaDummy205 D R S_cls E),
        (nb095AlphaDummy207 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy217 D R S_cls E) ≠
        (nb095AlphaDummy221 D R S_cls E) from (by
          unfold nb095AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy222 f) from (by
          unfold nb095AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb095AlphaDummy217 D R S_cls E) ≠ (nb095AlphaDummy221 D R S_cls E) from (by
          unfold nb095AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy222 f) from (by
          unfold nb095AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb095AlphaDummy221 D R S_cls E),
        (nb095AlphaDummy222 f)), ((nb095AlphaDummy217 D R S_cls E),
        (nb095AlphaDummy219 f)), ((nb095AlphaDummy218 D R S_cls E),
        (nb095AlphaDummy220 f)), ((nb095AlphaDummy243 D R S_cls E),
        (nb095AlphaDummy244 f)), ((nb095AlphaDummy241 D R S_cls E),
        (nb095AlphaDummy242 f)), ((nb095AlphaDummy210 D R S_cls E),
        (nb095AlphaDummy212 f)), ((nb095AlphaDummy209 D R S_cls E),
        (nb095AlphaDummy211 f)), ((nb095AlphaDummy239 D R S_cls E),
        (nb095AlphaDummy240 f)), ((nb095AlphaDummy213 D R S_cls E),
        (nb095AlphaDummy214 f)), ((nb095AlphaDummy206 D R S_cls E),
        (nb095AlphaDummy208 f)), ((nb095AlphaDummy205 D R S_cls E),
        (nb095AlphaDummy207 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb095AlphaDummy241 D R S_cls E), (nb095AlphaDummy242 f)),
                    ((nb095AlphaDummy210 D R S_cls E), (nb095AlphaDummy212 f)),
                    ((nb095AlphaDummy209 D R S_cls E), (nb095AlphaDummy211 f)),
                    ((nb095AlphaDummy239 D R S_cls E), (nb095AlphaDummy240 f)),
                    ((nb095AlphaDummy213 D R S_cls E), (nb095AlphaDummy214 f)),
                    ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
                    ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
                    ((nb095AlphaDummy001 D R S_cls E), u),
                    ((nb095AlphaDummy002 D R S_cls E), x),
                    ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0022`. -/
@[expose]
noncomputable def nb095SplitAlpha0022 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy213 D R S_cls E), (nb095AlphaDummy214 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy213 D R S_cls E)) (synCcompl
            (Class.cab (nb095AlphaDummy209 D R S_cls E)
              (synWrex (nb095AlphaDummy210 D R S_cls E)
                (Class.cv (nb095AlphaDummy206 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy213 D R S_cls E)) (synCcompl
              (Class.cab (nb095AlphaDummy209 D R S_cls E)
                (synWrex (nb095AlphaDummy210 D R S_cls E)
                  (Class.cv (nb095AlphaDummy205 D R S_cls E))
                  (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
                    (synCun (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy214 f)) (synCcompl
            (Class.cab (nb095AlphaDummy211 f)
              (synWrex (nb095AlphaDummy212 f) (Class.cv (nb095AlphaDummy208 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
                  (synCphi (Class.cv (nb095AlphaDummy212 f)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy214 f)) (synCcompl
              (Class.cab (nb095AlphaDummy211 f)
                (synWrex (nb095AlphaDummy212 f) (Class.cv (nb095AlphaDummy207 f))
                  (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
                    (synCun (synCphi (Class.cv (nb095AlphaDummy212 f)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy206 D R S_cls E) ≠
                              (nb095AlphaDummy210 D R S_cls E) from (by
                              unfold nb095AlphaDummy210;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0210 D R S_cls E)
                                      1))))
                          (show (nb095AlphaDummy208 f) ≠ (nb095AlphaDummy212 f) from (by
                              unfold nb095AlphaDummy212;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0212 f) 1))))
                          (TAlphaVar.there (show (nb095AlphaDummy206 D R S_cls E) ≠
                                (nb095AlphaDummy209 D R S_cls E) from (by
                                unfold nb095AlphaDummy209;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0210 D R S_cls E) 0))))
                            (show (nb095AlphaDummy208 f) ≠ (nb095AlphaDummy211 f) from (by
                                unfold nb095AlphaDummy211;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0212 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy206 D R S_cls E) ≠
                                  (nb095AlphaDummy215 D R S_cls E) from (by
                                  unfold nb095AlphaDummy215;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0214 D R S_cls E) 0))))
                              (show (nb095AlphaDummy208 f) ≠ (nb095AlphaDummy216 f) from
                                (by
                                  unfold nb095AlphaDummy216;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0215 f) 0))))
                              (TAlphaVar.there (show (nb095AlphaDummy206 D R S_cls E) ≠
                                    (nb095AlphaDummy213 D R S_cls E) from (by
                                    unfold nb095AlphaDummy213;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0211 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy208 f) ≠ (nb095AlphaDummy214 f) from (by
                                    unfold nb095AlphaDummy214;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0213 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy206 D R S_cls E))).fv ∪
                              ((Class.cv (nb095AlphaDummy205 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy208 f))).fv ∪
                              ((Class.cv (nb095AlphaDummy207 f))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy210 D R S_cls E) ≠
                                      (nb095AlphaDummy217 D R S_cls E) from (by
                                      unfold nb095AlphaDummy217;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0216 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy212 f) ≠ (nb095AlphaDummy219 f) from
                                    (by
                                      unfold nb095AlphaDummy219;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0217 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy210 D R S_cls E) ≠
                                        (nb095AlphaDummy218 D R S_cls E) from (by
                                        unfold nb095AlphaDummy218;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0216 D R S_cls E) 1)))) (show
                                      (nb095AlphaDummy212 f) ≠ (nb095AlphaDummy220 f) from
                                      (by
                                        unfold nb095AlphaDummy220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0217 f)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb095AlphaDummy210 D R S_cls E))).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv (nb095AlphaDummy212 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy217 D R S_cls E) ≠ (nb095AlphaDummy224 D R S_cls E) from (by
          unfold nb095AlphaDummy224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0220 D
                    R S_cls E)
                  1)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy227 f) from (by
          unfold nb095AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0221 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy217 D R S_cls E) ≠
        (nb095AlphaDummy223 D R S_cls E) from (by
          unfold nb095AlphaDummy223;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0220
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy226 f) from (by
          unfold nb095AlphaDummy226;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0221
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy217 D R S_cls E) ≠
        (nb095AlphaDummy221 D R S_cls E) from (by
          unfold nb095AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy222 f) from (by
          unfold nb095AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy225 D R S_cls E), (nb095AlphaDummy228 f)),
        ((nb095AlphaDummy224 D R S_cls E), (nb095AlphaDummy227 f)),
        ((nb095AlphaDummy223 D R S_cls E), (nb095AlphaDummy226 f)),
        ((nb095AlphaDummy221 D R S_cls E), (nb095AlphaDummy222 f)),
        ((nb095AlphaDummy217 D R S_cls E), (nb095AlphaDummy219 f)),
        ((nb095AlphaDummy218 D R S_cls E), (nb095AlphaDummy220 f)),
        ((nb095AlphaDummy210 D R S_cls E), (nb095AlphaDummy212 f)),
        ((nb095AlphaDummy209 D R S_cls E), (nb095AlphaDummy211 f)),
        ((nb095AlphaDummy215 D R S_cls E), (nb095AlphaDummy216 f)),
        ((nb095AlphaDummy213 D R S_cls E), (nb095AlphaDummy214 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠
        (nb095AlphaDummy231 D R S_cls E) from (by
          unfold
            nb095AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0224
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy232 f) from (by
          unfold
            nb095AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠
        (nb095AlphaDummy229 D R S_cls E) from (by
          unfold
            nb095AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0222
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy230 f) from (by
          unfold
            nb095AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy217
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy225
        D R S_cls E) ≠ (nb095AlphaDummy231 D R S_cls E) from (by
          unfold
            nb095AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0228
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy232 f) from (by
          unfold
            nb095AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy225 D R S_cls E) ≠
        (nb095AlphaDummy229 D R S_cls E) from (by
          unfold
            nb095AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0226
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy230 f) from (by
          unfold
            nb095AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠ (nb095AlphaDummy231
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0224
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy232 f) from (by
          unfold
            nb095AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠
        (nb095AlphaDummy229 D R S_cls E) from (by
          unfold
            nb095AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0222
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy230 f) from (by
          unfold
            nb095AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy217
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy225
        D R S_cls E) ≠ (nb095AlphaDummy231 D R S_cls E) from (by
          unfold
            nb095AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0228
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy232 f) from (by
          unfold
            nb095AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy225 D R S_cls E) ≠
        (nb095AlphaDummy229 D R S_cls E) from (by
          unfold
            nb095AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0226
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy230 f) from (by
          unfold
            nb095AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy225 D R S_cls E), (nb095AlphaDummy228 f)),
        ((nb095AlphaDummy224 D R S_cls E), (nb095AlphaDummy227 f)),
        ((nb095AlphaDummy223 D R S_cls E), (nb095AlphaDummy226 f)),
        ((nb095AlphaDummy221 D R S_cls E), (nb095AlphaDummy222 f)),
        ((nb095AlphaDummy217 D R S_cls E), (nb095AlphaDummy219 f)),
        ((nb095AlphaDummy218 D R S_cls E), (nb095AlphaDummy220 f)),
        ((nb095AlphaDummy210 D R S_cls E), (nb095AlphaDummy212 f)),
        ((nb095AlphaDummy209 D R S_cls E), (nb095AlphaDummy211 f)),
        ((nb095AlphaDummy215 D R S_cls E), (nb095AlphaDummy216 f)),
        ((nb095AlphaDummy213 D R S_cls E), (nb095AlphaDummy214 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy217 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy217
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy219 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠ (nb095AlphaDummy235
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0232
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy236 f) from (by
          unfold
            nb095AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠
        (nb095AlphaDummy233 D R S_cls E) from (by
          unfold
            nb095AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0230
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy234 f) from (by
          unfold
            nb095AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy217
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy224
        D R S_cls E) ≠ (nb095AlphaDummy235 D R S_cls E) from (by
          unfold
            nb095AlphaDummy235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0232
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy236 f) from (by
          unfold
            nb095AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠
        (nb095AlphaDummy233 D R S_cls E) from (by
          unfold
            nb095AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0230
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy234 f) from (by
          unfold
            nb095AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy217
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy225 D R S_cls E) ≠ (nb095AlphaDummy237
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0236
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy238 f) from (by
          unfold
            nb095AlphaDummy238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy225 D R S_cls E) ≠
        (nb095AlphaDummy233 D R S_cls E) from (by
          unfold
            nb095AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0234
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy234 f) from (by
          unfold
            nb095AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy225
        D R S_cls E) ≠ (nb095AlphaDummy237 D R S_cls E) from (by
          unfold
            nb095AlphaDummy237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0236
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy238 f) from (by
          unfold
            nb095AlphaDummy238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy225 D R S_cls E) ≠
        (nb095AlphaDummy233 D R S_cls E) from (by
          unfold
            nb095AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0234
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy234 f) from (by
          unfold
            nb095AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy217 D R S_cls E) ≠ (nb095AlphaDummy221 D R S_cls E) from (by
          unfold nb095AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy222 f) from (by
          unfold nb095AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy221 D R S_cls E), (nb095AlphaDummy222 f)),
        ((nb095AlphaDummy217 D R S_cls E), (nb095AlphaDummy219 f)),
        ((nb095AlphaDummy218 D R S_cls E), (nb095AlphaDummy220 f)),
        ((nb095AlphaDummy210 D R S_cls E), (nb095AlphaDummy212 f)),
        ((nb095AlphaDummy209 D R S_cls E), (nb095AlphaDummy211 f)),
        ((nb095AlphaDummy215 D R S_cls E), (nb095AlphaDummy216 f)),
        ((nb095AlphaDummy213 D R S_cls E), (nb095AlphaDummy214 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095AlphaDummy217 D R S_cls E) ≠ (nb095AlphaDummy221 D R S_cls E) from (by
          unfold nb095AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R S_cls E)
                  0)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy222 f) from (by
          unfold nb095AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy217 D R S_cls E) ≠ (nb095AlphaDummy221 D R S_cls E) from (by
          unfold nb095AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy222 f) from (by
          unfold nb095AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy221 D R S_cls E), (nb095AlphaDummy222 f)),
        ((nb095AlphaDummy217 D R S_cls E), (nb095AlphaDummy219 f)),
        ((nb095AlphaDummy218 D R S_cls E), (nb095AlphaDummy220 f)),
        ((nb095AlphaDummy210 D R S_cls E), (nb095AlphaDummy212 f)),
        ((nb095AlphaDummy209 D R S_cls E), (nb095AlphaDummy211 f)),
        ((nb095AlphaDummy215 D R S_cls E), (nb095AlphaDummy216 f)),
        ((nb095AlphaDummy213 D R S_cls E), (nb095AlphaDummy214 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy206 D R S_cls E) ≠
                              (nb095AlphaDummy210 D R S_cls E) from (by
                              unfold nb095AlphaDummy210;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0210 D R S_cls E)
                                      1))))
                          (show (nb095AlphaDummy208 f) ≠ (nb095AlphaDummy212 f) from (by
                              unfold nb095AlphaDummy212;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0212 f) 1))))
                          (TAlphaVar.there (show (nb095AlphaDummy206 D R S_cls E) ≠
                                (nb095AlphaDummy209 D R S_cls E) from (by
                                unfold nb095AlphaDummy209;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0210 D R S_cls E) 0))))
                            (show (nb095AlphaDummy208 f) ≠ (nb095AlphaDummy211 f) from (by
                                unfold nb095AlphaDummy211;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0212 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy206 D R S_cls E) ≠
                                  (nb095AlphaDummy215 D R S_cls E) from (by
                                  unfold nb095AlphaDummy215;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0214 D R S_cls E) 0))))
                              (show (nb095AlphaDummy208 f) ≠ (nb095AlphaDummy216 f) from
                                (by
                                  unfold nb095AlphaDummy216;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0215 f) 0))))
                              (TAlphaVar.there (show (nb095AlphaDummy206 D R S_cls E) ≠
                                    (nb095AlphaDummy213 D R S_cls E) from (by
                                    unfold nb095AlphaDummy213;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0211 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy208 f) ≠ (nb095AlphaDummy214 f) from (by
                                    unfold nb095AlphaDummy214;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0213 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy206 D R S_cls E))).fv ∪
                              ((Class.cv (nb095AlphaDummy205 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy208 f))).fv ∪
                              ((Class.cv (nb095AlphaDummy207 f))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy210 D R S_cls E) ≠
                                      (nb095AlphaDummy217 D R S_cls E) from (by
                                      unfold nb095AlphaDummy217;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0216 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy212 f) ≠ (nb095AlphaDummy219 f) from
                                    (by
                                      unfold nb095AlphaDummy219;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0217 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy210 D R S_cls E) ≠
                                        (nb095AlphaDummy218 D R S_cls E) from (by
                                        unfold nb095AlphaDummy218;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0216 D R S_cls E) 1)))) (show
                                      (nb095AlphaDummy212 f) ≠ (nb095AlphaDummy220 f) from
                                      (by
                                        unfold nb095AlphaDummy220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0217 f)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb095AlphaDummy210 D R S_cls E))).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv (nb095AlphaDummy212 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy217 D R S_cls E) ≠ (nb095AlphaDummy224 D R S_cls E) from (by
          unfold nb095AlphaDummy224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0220 D
                    R S_cls E)
                  1)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy227 f) from (by
          unfold nb095AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0221 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy217 D R S_cls E) ≠
        (nb095AlphaDummy223 D R S_cls E) from (by
          unfold nb095AlphaDummy223;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0220
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy226 f) from (by
          unfold nb095AlphaDummy226;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0221
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy217 D R S_cls E) ≠
        (nb095AlphaDummy221 D R S_cls E) from (by
          unfold nb095AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy222 f) from (by
          unfold nb095AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy225 D R S_cls E), (nb095AlphaDummy228 f)),
        ((nb095AlphaDummy224 D R S_cls E), (nb095AlphaDummy227 f)),
        ((nb095AlphaDummy223 D R S_cls E), (nb095AlphaDummy226 f)),
        ((nb095AlphaDummy221 D R S_cls E), (nb095AlphaDummy222 f)),
        ((nb095AlphaDummy217 D R S_cls E), (nb095AlphaDummy219 f)),
        ((nb095AlphaDummy218 D R S_cls E), (nb095AlphaDummy220 f)),
        ((nb095AlphaDummy210 D R S_cls E), (nb095AlphaDummy212 f)),
        ((nb095AlphaDummy209 D R S_cls E), (nb095AlphaDummy211 f)),
        ((nb095AlphaDummy215 D R S_cls E), (nb095AlphaDummy216 f)),
        ((nb095AlphaDummy213 D R S_cls E), (nb095AlphaDummy214 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠
        (nb095AlphaDummy231 D R S_cls E) from (by
          unfold
            nb095AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0224
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy232 f) from (by
          unfold
            nb095AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠
        (nb095AlphaDummy229 D R S_cls E) from (by
          unfold
            nb095AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0222
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy230 f) from (by
          unfold
            nb095AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy217
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy225
        D R S_cls E) ≠ (nb095AlphaDummy231 D R S_cls E) from (by
          unfold
            nb095AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0228
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy232 f) from (by
          unfold
            nb095AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy225 D R S_cls E) ≠
        (nb095AlphaDummy229 D R S_cls E) from (by
          unfold
            nb095AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0226
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy230 f) from (by
          unfold
            nb095AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠ (nb095AlphaDummy231
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0224
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy232 f) from (by
          unfold
            nb095AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠
        (nb095AlphaDummy229 D R S_cls E) from (by
          unfold
            nb095AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0222
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy230 f) from (by
          unfold
            nb095AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy217
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy225
        D R S_cls E) ≠ (nb095AlphaDummy231 D R S_cls E) from (by
          unfold
            nb095AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0228
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy232 f) from (by
          unfold
            nb095AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy225 D R S_cls E) ≠
        (nb095AlphaDummy229 D R S_cls E) from (by
          unfold
            nb095AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0226
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy230 f) from (by
          unfold
            nb095AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy225 D R S_cls E), (nb095AlphaDummy228 f)),
        ((nb095AlphaDummy224 D R S_cls E), (nb095AlphaDummy227 f)),
        ((nb095AlphaDummy223 D R S_cls E), (nb095AlphaDummy226 f)),
        ((nb095AlphaDummy221 D R S_cls E), (nb095AlphaDummy222 f)),
        ((nb095AlphaDummy217 D R S_cls E), (nb095AlphaDummy219 f)),
        ((nb095AlphaDummy218 D R S_cls E), (nb095AlphaDummy220 f)),
        ((nb095AlphaDummy210 D R S_cls E), (nb095AlphaDummy212 f)),
        ((nb095AlphaDummy209 D R S_cls E), (nb095AlphaDummy211 f)),
        ((nb095AlphaDummy215 D R S_cls E), (nb095AlphaDummy216 f)),
        ((nb095AlphaDummy213 D R S_cls E), (nb095AlphaDummy214 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy217 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy217
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy219 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠ (nb095AlphaDummy235
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0232
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy236 f) from (by
          unfold
            nb095AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠
        (nb095AlphaDummy233 D R S_cls E) from (by
          unfold
            nb095AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0230
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy234 f) from (by
          unfold
            nb095AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy217
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy224
        D R S_cls E) ≠ (nb095AlphaDummy235 D R S_cls E) from (by
          unfold
            nb095AlphaDummy235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0232
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy236 f) from (by
          unfold
            nb095AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy224 D R S_cls E) ≠
        (nb095AlphaDummy233 D R S_cls E) from (by
          unfold
            nb095AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0230
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy234 f) from (by
          unfold
            nb095AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy217
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy225 D R S_cls E) ≠ (nb095AlphaDummy237
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0236
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy238 f) from (by
          unfold
            nb095AlphaDummy238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy225 D R S_cls E) ≠
        (nb095AlphaDummy233 D R S_cls E) from (by
          unfold
            nb095AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0234
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy234 f) from (by
          unfold
            nb095AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy225
        D R S_cls E) ≠ (nb095AlphaDummy237 D R S_cls E) from (by
          unfold
            nb095AlphaDummy237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0236
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy238 f) from (by
          unfold
            nb095AlphaDummy238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy225 D R S_cls E) ≠
        (nb095AlphaDummy233 D R S_cls E) from (by
          unfold
            nb095AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0234
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy228 f) ≠ (nb095AlphaDummy234 f) from (by
          unfold
            nb095AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy217 D R S_cls E) ≠ (nb095AlphaDummy221 D R S_cls E) from (by
          unfold nb095AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy222 f) from (by
          unfold nb095AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy221 D R S_cls E), (nb095AlphaDummy222 f)),
        ((nb095AlphaDummy217 D R S_cls E), (nb095AlphaDummy219 f)),
        ((nb095AlphaDummy218 D R S_cls E), (nb095AlphaDummy220 f)),
        ((nb095AlphaDummy210 D R S_cls E), (nb095AlphaDummy212 f)),
        ((nb095AlphaDummy209 D R S_cls E), (nb095AlphaDummy211 f)),
        ((nb095AlphaDummy215 D R S_cls E), (nb095AlphaDummy216 f)),
        ((nb095AlphaDummy213 D R S_cls E), (nb095AlphaDummy214 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095AlphaDummy217 D R S_cls E) ≠ (nb095AlphaDummy221 D R S_cls E) from (by
          unfold nb095AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R S_cls E)
                  0)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy222 f) from (by
          unfold nb095AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy217 D R S_cls E) ≠ (nb095AlphaDummy221 D R S_cls E) from (by
          unfold nb095AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy222 f) from (by
          unfold nb095AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy221 D R S_cls E), (nb095AlphaDummy222 f)),
        ((nb095AlphaDummy217 D R S_cls E), (nb095AlphaDummy219 f)),
        ((nb095AlphaDummy218 D R S_cls E), (nb095AlphaDummy220 f)),
        ((nb095AlphaDummy210 D R S_cls E), (nb095AlphaDummy212 f)),
        ((nb095AlphaDummy209 D R S_cls E), (nb095AlphaDummy211 f)),
        ((nb095AlphaDummy215 D R S_cls E), (nb095AlphaDummy216 f)),
        ((nb095AlphaDummy213 D R S_cls E), (nb095AlphaDummy214 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb095SplitAlpha0021 x u D R S_cls f E)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex
                    (TAlphaWff.neg (nb095SplitAlpha0021 x u D R S_cls f E)))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
